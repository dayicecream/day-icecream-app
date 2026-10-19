import base64
import csv
import datetime
import io
import json
import math
import os
import re
import shutil
import socket
import subprocess
import time
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
import zipfile
from pathlib import Path

import folium
import numpy as np
import qrcode
import streamlit as st
import streamlit.components.v1 as components
from PIL import Image, ImageChops, ImageDraw, ImageFilter, ImageOps


def _enable_pwa_service_worker_allowed_header() -> None:
    """
    ปลดล็อก HTTP Header 'Service-Worker-Allowed: /' เฉพาะเมื่อเบราว์เซอร์ร้องขอไฟล์ sw.js หรือ manifest.json เท่านั้น
    ปลอดภัย 100% ไม่กระทบหน้าเว็บหลักหรือไฟล์อื่นของระบบ ทำให้ Google Chrome และ Samsung Internet
    ลงทะเบียน Service Worker ที่ Root Scope ("/") และเด้งหน้าต่าง [ติดตั้งแอป] อัตโนมัติในคลิกเดียว
    """
    try:
        from starlette.responses import FileResponse as _StarletteFileResponse

        if not getattr(_StarletteFileResponse, "_day_pwa_sw_patched", False):
            _orig_init_headers = _StarletteFileResponse.init_headers

            def _patched_init_headers(self, headers=None):  # type: ignore
                _orig_init_headers(self, headers)
                try:
                    p_str = str(getattr(self, "path", "") or "").replace("\\", "/").lower()
                    if p_str.endswith("/sw.js") or p_str.endswith("/manifest.json"):
                        self.headers["Service-Worker-Allowed"] = "/"
                        self.headers["Cache-Control"] = "no-cache"
                except Exception:
                    pass

            _StarletteFileResponse.init_headers = _patched_init_headers  # type: ignore
            _StarletteFileResponse._day_pwa_sw_patched = True  # type: ignore
    except Exception:
        pass


_enable_pwa_service_worker_allowed_header()

# ==============================================================================
# PATHS & CONFIGURATION FILES
# ==============================================================================
APP_DIR = Path(__file__).resolve().parent
ASSETS_DIR = APP_DIR / "assets"
FLAVORS_IMG_DIR = ASSETS_DIR / "flavors"
PROMO_GALLERY_DIR = APP_DIR / "promo_gallery"
TOOLS_DIR = APP_DIR / "tools"
CLOUDFLARED_EXE_PATH = TOOLS_DIR / "cloudflared.exe"
TUNNEL_LOG_PATH = TOOLS_DIR / "tunnel.log"
ACTIVE_TUNNEL_JSON_PATH = TOOLS_DIR / "active_tunnel.json"

LINKS_CONFIG_PATH = APP_DIR / "links_config.json"
CHANNELS_CONFIG_PATH = APP_DIR / "channels_config.json"
FLAVORS_CONFIG_PATH = APP_DIR / "flavors_config.json"
PROMO_GALLERY_CONFIG_PATH = APP_DIR / "promo_gallery_config.json"
BRANCHES_CACHE_PATH = APP_DIR / "branches_cache.json"
VIP_CUSTOMERS_CSV_SPACE_PATH = APP_DIR / "vip_customers_ orders.csv"
VIP_CUSTOMERS_CSV_CLEAN_PATH = APP_DIR / "vip_customers_orders.csv"

CUSTOM_PIN_PATH = APP_DIR / "custom_pin.png"
CUSTOM_PIN_INTERNAL_PATH = APP_DIR / "custom_pin_internal.png"

F_DRIVE_5OZ_ROOT = Path(
    r"F:\Dayicecream องค์ประกอบสำหรับหนัง\ข้อมูล ถ้วยไอศครีมแบบถ้วยบรรจุสำเร็จ 5oz + ป้ายทั้งหมดของเก่า"
)
F_DRIVE_MAIN_LOGO = F_DRIVE_5OZ_ROOT / "โลโก้ เดย์ไอศครีม.jpg"
F_DRIVE_QUALITY_BANNER = F_DRIVE_5OZ_ROOT / "สำหรับแฟรนไชส์ทั่วประเทศ2565 - ราคา 45บาท.jpg"

LINKTREE_URL = "https://linktr.ee/Dayicecream"
GOOGLE_MY_MAPS_KML_URL = (
    "https://www.google.com/maps/d/kml?mid=1s7u3Q42kE1mFt6QylaWVa8JYYp-h9DGH&forcekml=1"
)
GOOGLE_MY_MAPS_VIEWER_URL = (
    "https://www.google.com/maps/d/viewer?mid=1s7u3Q42kE1mFt6QylaWVa8JYYp-h9DGH"
)
INTERNAL_STATUS_KEYWORDS = ["จอง", "เก็บตู้", "ยกเลิก"]

DEFAULT_HQ_LAT = 13.8246901
DEFAULT_HQ_LON = 100.0570871


@st.cache_data(show_spinner=False)
def load_b64_image(path_str: str) -> str:
    p = Path(path_str)
    if p.exists():
        try:
            return base64.b64encode(p.read_bytes()).decode("ascii")
        except Exception:
            return ""
    return ""


def render_html(html_str: str) -> None:
    """
    ยุบรวม HTML เป็นบรรทัดเดียวติดกันด้วย re.sub(r'\\n\\s*', '', ...) ก่อนส่งเข้า st.markdown
    เพื่อป้องกันไม่ให้ CommonMark / Markdown ตีความ HTML เป็น Code Block หรือหลุดแท็ก <div> ออกมา 100%
    """
    if "<style>" in html_str:
        cleaned = "\n".join(line.lstrip() for line in html_str.splitlines() if line.strip())
    else:
        cleaned = re.sub(r"\n\s*", " ", html_str.strip())
        cleaned = re.sub(r">\s+<", "><", cleaned)
    st.markdown(cleaned, unsafe_allow_html=True)


def get_local_lan_url(port: int = 8502) -> str:
    """ดึงเลข Local IP ของเครื่องคอมพิวเตอร์อัตโนมัติ เช่น http://192.168.1.109:8502"""
    ip_addr = "127.0.0.1"
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.settimeout(1.0)
        s.connect(("8.8.8.8", 80))
        ip_addr = s.getsockname()[0]
        s.close()
    except Exception:
        try:
            ip_addr = socket.gethostbyname(socket.gethostname())
        except Exception:
            ip_addr = "127.0.0.1"
    return f"http://{ip_addr}:{port}"


@st.cache_data(show_spinner=False)
def generate_qr_code_bytes(url: str) -> bytes:
    """สร้างภาพ QR Code คมชัดพร้อมขอบสีขาวสะอาดตาสำหรับสแกนด้วยกล้องมือถือ"""
    qr = qrcode.QRCode(
        version=1,
        error_correction=qrcode.constants.ERROR_CORRECT_M,
        box_size=8,
        border=3,
    )
    qr.add_data(url)
    qr.make(fit=True)
    img = qr.make_image(fill_color="#2B1810", back_color="#FFFFFF").convert("RGB")
    buf = io.BytesIO()
    img.save(buf, format="PNG")
    return buf.getvalue()


PRODUCTION_APP_URL = "https://app.dayicecream.com"
RENDER_CLOUD_URL = "https://day-icecream-app.onrender.com"


def get_existing_online_tunnel_url() -> str:
    """คืนค่าโดเมนจริงของเว็บแอป Day Ice Cream (ไม่ใช้ลิงก์ชั่วคราว trycloudflare ตัวเก่า)"""
    return PRODUCTION_APP_URL


def start_online_mobile_tunnel(port: int = 8502) -> tuple[str, str]:
    """คืนค่าลิงก์ Cloud ถาวรของแอป Day Ice Cream"""
    _ = port
    return PRODUCTION_APP_URL, "เชื่อมต่อโดเมนหลัก https://app.dayicecream.com (และ https://day-icecream-app.onrender.com) เรียบร้อย"

    # 2. Fallback: pyngrok (หากติดตั้งและตั้งค่าไว้)
    try:
        from pyngrok import ngrok  # type: ignore

        tunnel = ngrok.connect(port, "http")
        pub_url = tunnel.public_url.replace("http://", "https://")
        ACTIVE_TUNNEL_JSON_PATH.write_text(
            json.dumps(
                {
                    "public_url": pub_url,
                    "updated_at": time.strftime("%Y-%m-%d %H:%M:%S"),
                },
                ensure_ascii=False,
                indent=2,
            ),
            encoding="utf-8",
        )
        return pub_url, "pyngrok Tunnel"
    except Exception:
        pass

    return "", "ไม่สามารถสร้างลิงก์ออนไลน์ได้ในขณะนี้ กรุณาใช้ QR Code Wi-Fi เดียวกันด้านบนครับ"



# ==============================================================================
# PILLOW (PIL) CUSTOM PIN ICON GENERATOR (custom_pin.png + Base64 Data URI)
# ==============================================================================
def ensure_custom_pin_icons(force: bool = False) -> tuple[str, str]:
    """
    สร้างไฟล์ไอคอนหมุดวงกลมขอบขาวมีเงา (custom_pin.png ขนาด 42x42 พิกเซล พื้นหลังใส .png)
    และหมุดสถานะภายในขอบแดง-เทา (custom_pin_internal.png) จากรูปโลโก้น้องผู้ชายถือไอศกรีมของพี่เดย์
    """
    APP_DIR.mkdir(parents=True, exist_ok=True)
    ASSETS_DIR.mkdir(parents=True, exist_ok=True)

    if not force and CUSTOM_PIN_PATH.exists() and CUSTOM_PIN_INTERNAL_PATH.exists():
        b64_pub = load_b64_image(str(CUSTOM_PIN_PATH))
        b64_int = load_b64_image(str(CUSTOM_PIN_INTERNAL_PATH))
        if b64_pub and b64_int:
            return (
                f"data:image/png;base64,{b64_pub}",
                f"data:image/png;base64,{b64_int}",
            )

    candidate_sources = [
        F_DRIVE_MAIN_LOGO,
        ASSETS_DIR / "day_icecream_mascot_source.jpg",
        ASSETS_DIR / "kmz_icon_1.png",
        Path(
            r"F:\Day Ice Cream - Global Art Studio\002_logos\DayIceCream_Official_Logo_BoyMascot_Compact.png"
        ),
        APP_DIR / "day_icecream_logo.png",
    ]
    src_path = next((p for p in candidate_sources if p.exists()), None)
    if src_path is None:
        return "", ""

    img = Image.open(src_path).convert("RGBA")
    bg = Image.new("RGBA", img.size, (255, 255, 255, 255))
    diff = ImageChops.difference(img, bg).convert("L")
    bbox = diff.point(lambda x: 255 if x > 18 else 0).getbbox()
    cropped = img.crop(bbox) if bbox else img

    arr = np.array(cropped)
    white_mask = (arr[:, :, 0] > 246) & (arr[:, :, 1] > 246) & (arr[:, :, 2] > 246)
    arr[white_mask, 3] = 0
    cropped_transparent = Image.fromarray(arr, "RGBA")

    def render_badge(
        logo_rgba: Image.Image,
        out_size: int = 42,
        outer_border: tuple = (255, 255, 255, 255),
        inner_ring: tuple = (226, 232, 240, 255),
        bg_fill: tuple = (255, 255, 255, 255),
    ) -> Image.Image:
        scale = 4
        s_px = out_size * scale
        canvas = Image.new("RGBA", (s_px, s_px), (0, 0, 0, 0))
        pad = int(2.5 * scale)

        shadow = Image.new("RGBA", (s_px, s_px), (0, 0, 0, 0))
        sdraw = ImageDraw.Draw(shadow)
        sdraw.ellipse(
            [pad, pad + int(1.2 * scale), s_px - pad, s_px - pad + int(1.2 * scale)],
            fill=(0, 0, 0, 160),
        )
        shadow = shadow.filter(ImageFilter.GaussianBlur(2.0 * scale))
        canvas.alpha_composite(shadow)

        circle_layer = Image.new("RGBA", (s_px, s_px), (0, 0, 0, 0))
        cdraw = ImageDraw.Draw(circle_layer)
        cdraw.ellipse([pad, pad, s_px - pad, s_px - pad], fill=bg_fill)

        max_dim = int((s_px - 2 * pad) * 0.88)
        logo_copy = logo_rgba.copy()
        logo_copy.thumbnail((max_dim, max_dim), Image.Resampling.LANCZOS)
        lx = (s_px - logo_copy.width) // 2
        ly = (s_px - logo_copy.height) // 2 - int(0.5 * scale)
        circle_layer.alpha_composite(logo_copy, (lx, ly))

        mask = Image.new("L", (s_px, s_px), 0)
        ImageDraw.Draw(mask).ellipse([pad, pad, s_px - pad, s_px - pad], fill=255)
        clipped = Image.new("RGBA", (s_px, s_px), (0, 0, 0, 0))
        clipped.paste(circle_layer, (0, 0), mask)
        canvas.alpha_composite(clipped)

        bdraw = ImageDraw.Draw(canvas)
        bdraw.ellipse(
            [pad, pad, s_px - pad, s_px - pad],
            outline=outer_border,
            width=int(2.6 * scale),
        )
        if inner_ring:
            ipad = pad + int(2.2 * scale)
            bdraw.ellipse(
                [ipad, ipad, s_px - ipad, s_px - ipad],
                outline=inner_ring,
                width=int(1.4 * scale),
            )

        return canvas.resize((out_size, out_size), Image.Resampling.LANCZOS)

    pin_public = render_badge(
        cropped_transparent,
        out_size=42,
        outer_border=(255, 255, 255, 255),
        inner_ring=(226, 232, 240, 255),
        bg_fill=(255, 255, 255, 255),
    )
    pin_internal = render_badge(
        cropped_transparent,
        out_size=42,
        outer_border=(220, 38, 38, 255),
        inner_ring=(100, 116, 139, 255),
        bg_fill=(241, 245, 249, 255),
    )

    pin_public.save(CUSTOM_PIN_PATH, format="PNG")
    pin_public.save(ASSETS_DIR / "custom_pin.png", format="PNG")
    pin_internal.save(CUSTOM_PIN_INTERNAL_PATH, format="PNG")
    pin_internal.save(ASSETS_DIR / "custom_pin_internal.png", format="PNG")

    load_b64_image.clear()
    b64_pub = load_b64_image(str(CUSTOM_PIN_PATH))
    b64_int = load_b64_image(str(CUSTOM_PIN_INTERNAL_PATH))
    return f"data:image/png;base64,{b64_pub}", f"data:image/png;base64,{b64_int}"


@st.cache_data(show_spinner=False)
def ensure_pwa_app_icons(icon_version: str = "v005_direct") -> dict[str, str]:
    """
    เตรียมไอคอนแอปหลักจาก 'โลโก้ app 004.jpg' ครอปขอบสีขาวด้านนอกออก 100%
    บันทึกที่ F:\\DAY_ICECREAM_BRANCH_APP\\app_icon_512.png (512x512 px)
    และบันทึกในโฟลเดอร์ static/ (/app/static/manifest.json, app_icon_192.png, app_icon_512.png, sw.js)
    เพื่อให้ Google Chrome ยิง beforeinstallprompt ติดตั้งแอปได้ในคลิกเดียว
    """
    APP_DIR.mkdir(parents=True, exist_ok=True)
    ASSETS_DIR.mkdir(parents=True, exist_ok=True)
    static_dir = APP_DIR / "static"
    static_dir.mkdir(parents=True, exist_ok=True)

    raw_004_path = APP_DIR / "โลโก้ app 004.jpg"
    icon_512_path = APP_DIR / "app_icon_512.png"
    square_192_path = ASSETS_DIR / "pwa_app_icon_192.png"
    square_180_path = ASSETS_DIR / "pwa_app_icon_180.png"
    icon_ico_path = APP_DIR / "day_icecream_icon.ico"

    if raw_004_path.exists():
        try:
            need_build = (
                not icon_512_path.exists()
                or not square_192_path.exists()
                or not square_180_path.exists()
                or icon_512_path.stat().st_mtime < raw_004_path.stat().st_mtime
            )
            if need_build:
                im = Image.open(raw_004_path).convert("RGBA")
                w, h = im.size
                mid_y = h // 2
                mid_x = w // 2
                px = im.load()
                left = next((x for x in range(w) if sum(px[x, mid_y][:3]) / 3 < 240), 4)
                right = next((x for x in range(w - 1, -1, -1) if sum(px[x, mid_y][:3]) / 3 < 240), w - 4)
                top = next((y for y in range(h) if sum(px[mid_x, y][:3]) / 3 < 240), 3)
                bottom = next((y for y in range(h - 1, -1, -1) if sum(px[mid_x, y][:3]) / 3 < 240), h - 3)

                cropped = im.crop((left + 1, top + 1, right, bottom))
                icon_512 = cropped.resize((512, 512), Image.Resampling.LANCZOS)

                # ลบพื้นสีขาวบริเวณมุมโค้งด้านนอกของกรอบทองให้โปร่งใส 100%
                ImageDraw.floodfill(icon_512, (0, 0), (0, 0, 0, 0), thresh=38)
                ImageDraw.floodfill(icon_512, (511, 0), (0, 0, 0, 0), thresh=38)
                ImageDraw.floodfill(icon_512, (0, 511), (0, 0, 0, 0), thresh=38)
                ImageDraw.floodfill(icon_512, (511, 511), (0, 0, 0, 0), thresh=38)

                icon_512.save(icon_512_path, format="PNG")
                icon_512.resize((192, 192), Image.Resampling.LANCZOS).save(square_192_path, format="PNG")
                icon_512.resize((180, 180), Image.Resampling.LANCZOS).save(square_180_path, format="PNG")
                load_b64_image.clear()
        except Exception:
            pass

    # คัดลอกไฟล์ไอคอนและสร้าง manifest.json + sw.js ลงในโฟลเดอร์ static/ สำหรับ Same-Origin PWA
    try:
        if icon_512_path.exists():
            shutil.copy2(icon_512_path, static_dir / "app_icon_512.png")
        if square_192_path.exists():
            shutil.copy2(square_192_path, static_dir / "app_icon_192.png")
        if square_180_path.exists():
            shutil.copy2(square_180_path, static_dir / "app_icon_180.png")

        static_manifest_obj = {
            "id": "/",
            "name": "Day Ice Cream (เดย์ ไอศกรีม)",
            "short_name": "Day Ice Cream",
            "description": "สั่งไอศกรีมโฮมเมดพรีเมียม 30 รสชาติ ค้นหา 300+ สาขาทั่วไทย และสมัครแฟรนไชส์กำไร 100%",
            "start_url": "/",
            "scope": "/",
            "display": "standalone",
            "orientation": "portrait",
            "background_color": "#FFF8F0",
            "theme_color": "#d32f2f",
            "icons": [
                {
                    "src": "/app/static/app_icon_192.png",
                    "sizes": "192x192",
                    "type": "image/png",
                    "purpose": "any maskable",
                },
                {
                    "src": "/app/static/app_icon_192.png",
                    "sizes": "192x192",
                    "type": "image/png",
                    "purpose": "any",
                },
                {
                    "src": "/app/static/app_icon_192.png",
                    "sizes": "192x192",
                    "type": "image/png",
                    "purpose": "maskable",
                },
                {
                    "src": "/app/static/app_icon_512.png",
                    "sizes": "512x512",
                    "type": "image/png",
                    "purpose": "any maskable",
                },
                {
                    "src": "/app/static/app_icon_512.png",
                    "sizes": "512x512",
                    "type": "image/png",
                    "purpose": "any",
                },
                {
                    "src": "/app/static/app_icon_512.png",
                    "sizes": "512x512",
                    "type": "image/png",
                    "purpose": "maskable",
                },
            ],
        }
        (static_dir / "manifest.json").write_text(
            json.dumps(static_manifest_obj, ensure_ascii=False, indent=2),
            encoding="utf-8",
        )
        (static_dir / "sw.js").write_text(
            'self.addEventListener("install",function(e){self.skipWaiting();});\n'
            'self.addEventListener("activate",function(e){e.waitUntil(self.clients.claim());});\n'
            'self.addEventListener("fetch",function(e){\n'
            '  if(e.request.mode==="navigate"){\n'
            '    e.respondWith(fetch(e.request).catch(function(){return caches.match(e.request);}));\n'
            '  }\n'
            '});\n',
            encoding="utf-8",
        )
    except Exception:
        pass

    icon_512_b64 = load_b64_image(str(icon_512_path)) if icon_512_path.exists() else ""
    square_192_b64 = (
        load_b64_image(str(square_192_path))
        if square_192_path.exists()
        else icon_512_b64
    )
    square_180_b64 = (
        load_b64_image(str(square_180_path))
        if square_180_path.exists()
        else square_192_b64
    )
    icon_ico_b64 = load_b64_image(str(icon_ico_path)) if icon_ico_path.exists() else square_192_b64

    manifest_obj = {
        "name": "Day Ice Cream (เดย์ ไอศกรีม)",
        "short_name": "Day Ice Cream",
        "description": "สั่งไอศกรีมโฮมเมดพรีเมียม 30 รสชาติ ค้นหา 300+ สาขาทั่วไทย และสมัครแฟรนไชส์กำไร 100% (app.dayicecream.com / www.dayicecream.com)",
        "start_url": "/",
        "scope": "/",
        "display": "standalone",
        "orientation": "portrait",
        "background_color": "#FFF8F0",
        "theme_color": "#d32f2f",
        "icons": [
            {
                "src": f"data:image/png;base64,{square_192_b64}",
                "sizes": "192x192",
                "type": "image/png",
                "purpose": "any",
            },
            {
                "src": f"data:image/png;base64,{icon_512_b64 or square_192_b64}",
                "sizes": "512x512",
                "type": "image/png",
                "purpose": "any",
            },
        ],
    }
    manifest_json_bytes = json.dumps(manifest_obj, ensure_ascii=False).encode("utf-8")
    manifest_b64 = base64.b64encode(manifest_json_bytes).decode("utf-8")

    return {
        "logo_png_b64": icon_512_b64 or square_192_b64,
        "icon_512_b64": icon_512_b64 or square_192_b64,
        "icon_180_b64": square_180_b64,
        "icon_ico_b64": icon_ico_b64,
        "square_192_b64": square_192_b64,
        "manifest_b64": manifest_b64,
        "iphone_mockup_b64": icon_512_b64 or square_192_b64,
        "qr_app_004_b64": "",
    }


REAL_QR_SOURCE_DIR = APP_DIR / "banners_4k_source"
REAL_QR_4K_DIR = APP_DIR / "banners_4k_real_qr"
REAL_QR_MAIN_WEB_DIR = APP_DIR / "banners_4k_main_web_qr"
REAL_QR_4K_WWW_DIR = REAL_QR_4K_DIR / "www"
REAL_QR_WEB_1080P_DIR = REAL_QR_4K_DIR / "web_1080p"


@st.cache_data(max_entries=4, show_spinner=False)
def get_real_qr_banner_web_b64(banner_num: str = "011", ver: str = "v3_web_fast") -> str:
    """
    โหลดภาพแบนเนอร์ 4K ที่แปะ QR Code จริงสแกนติด 100% (ย่อขนาด Web HD 1280x714 ~160 KB
    เพื่อให้โหลดผ่านมือถือ 4G/5G และ TikTok/Facebook เร็วภายในเสี้ยววินาที และไม่กิน RAM เซิร์ฟเวอร์)
    """
    _ = ver
    b_num = banner_num.strip().zfill(3)
    REAL_QR_WEB_1080P_DIR.mkdir(parents=True, exist_ok=True)
    fast_web_p = REAL_QR_WEB_1080P_DIR / f"Web_banner_fast_{b_num}_REAL_QR.jpg"
    if fast_web_p.exists():
        return base64.b64encode(fast_web_p.read_bytes()).decode("utf-8")

    web_p = REAL_QR_WEB_1080P_DIR / f"Web_banner_4K_{b_num}_REAL_QR.jpg"
    full_p = REAL_QR_4K_DIR / f"Web_banner_4K_{b_num}_REAL_QR.jpg"
    target_p = web_p if web_p.exists() else full_p
    if target_p.exists():
        try:
            with Image.open(target_p) as im:
                rgb = im.convert("RGB")
                rgb.thumbnail((1280, 714), Image.Resampling.LANCZOS)
                buf = io.BytesIO()
                rgb.save(buf, format="JPEG", quality=84, optimize=True)
                raw_jpg = buf.getvalue()
            try:
                fast_web_p.write_bytes(raw_jpg)
            except Exception:
                pass
            return base64.b64encode(raw_jpg).decode("utf-8")
        except Exception:
            return base64.b64encode(target_p.read_bytes()).decode("utf-8")
    return ""


@st.cache_data(max_entries=2, show_spinner=False)
def get_real_qr_banner_4k_bytes(banner_num: str = "011", domain_mode: str = "app") -> bytes:
    """
    โหลดไฟล์ภาพแบนเนอร์ 4K ต้นฉบับความละเอียดสูง (5504 x 3072 px) ที่แปะ QR Code จริงแล้ว
    domain_mode: 'app' -> https://app.dayicecream.com (banners_4k_real_qr)
                 'www' -> https://www.dayicecream.com (banners_4k_main_web_qr)
    """
    b_num = banner_num.strip().zfill(3)
    if domain_mode == "www":
        p_main = REAL_QR_MAIN_WEB_DIR / f"Web_banner_4K_{b_num}_MAIN_WEB_QR.jpg"
        p_plain = REAL_QR_MAIN_WEB_DIR / f"Web_banner_4K_{b_num}.jpg"
        p_old = REAL_QR_4K_WWW_DIR / f"Web_banner_4K_{b_num}_WWW_REAL_QR.jpg"
        for cand in (p_main, p_plain, p_old):
            if cand.exists():
                return cand.read_bytes()
    else:
        p_rq = REAL_QR_4K_DIR / f"Web_banner_4K_{b_num}_REAL_QR.jpg"
        p_plain = REAL_QR_4K_DIR / f"Web_banner_4K_{b_num}.jpg"
        for cand in (p_rq, p_plain):
            if cand.exists():
                return cand.read_bytes()
    return b""


@st.cache_data(max_entries=1, show_spinner=False)
def get_makewebeasy_banner_bytes(banner_ver: str = "v004_pizza") -> bytes:
    """
    โหลดหรือสร้างไฟล์แบนเนอร์แนวยาว MAKEWEBEASY_APP_BANNER.png (1920 x 450 px)
    สไตล์ The Pizza Company สำหรับนำไปแปะบนเว็บหลัก www.dayicecream.com
    """
    _ = banner_ver
    banner_p = APP_DIR / "MAKEWEBEASY_APP_BANNER.png"
    if banner_p.exists():
        return banner_p.read_bytes()
    try:
        from generate_makewebeasy_banner import build_makewebeasy_pizza_style_banner

        return build_makewebeasy_pizza_style_banner(
            target_url="https://app.dayicecream.com",
            save_path=banner_p,
        )
    except Exception:
        return b""


@st.cache_data(max_entries=2, show_spinner=False)
def get_printable_a4_poster_bytes(
    target_url: str = "https://app.dayicecream.com",
    force_regenerate: bool = False,
    poster_ver: str = "v004_gold",
) -> bytes:
    """
    โหลดหรือสร้างไฟล์โปสเตอร์ QR Code ขนาด A4 ความละเอียดสูง (2480 x 3508 px, 300 DPI)
    สำหรับปริ้นท์ตั้งที่โรงงานและหน้าร้านสาขา (QR_CODE_POSTER_FOR_PRINT.png)
    """
    _ = poster_ver
    default_app_poster = APP_DIR / "QR_CODE_POSTER_FOR_PRINT.png"
    default_www_poster = APP_DIR / "QR_CODE_POSTER_WWW_FOR_PRINT.png"

    clean_u = target_url.strip().rstrip("/").lower()
    if not force_regenerate:
        if clean_u in ("https://app.dayicecream.com", "http://app.dayicecream.com") and default_app_poster.exists():
            return default_app_poster.read_bytes()
        if clean_u in ("https://www.dayicecream.com", "http://www.dayicecream.com") and default_www_poster.exists():
            return default_www_poster.read_bytes()

    try:
        from generate_qr_poster import build_a4_qr_poster_image

        save_target = None
        if clean_u in ("https://app.dayicecream.com", "http://app.dayicecream.com"):
            save_target = default_app_poster
        elif clean_u in ("https://www.dayicecream.com", "http://www.dayicecream.com"):
            save_target = default_www_poster
        return build_a4_qr_poster_image(target_url=target_url, save_path=save_target)
    except Exception:
        if default_app_poster.exists():
            return default_app_poster.read_bytes()
        return b""


# ==============================================================================
# SCAN 30 FLAVORS FROM F:\ DRIVE & MANAGE STOCK (flavors_config.json)
# ==============================================================================
INITIAL_30_FLAVORS = [
    {"id": 1,  "name": "ไอศครีมมะพร้าว น้ำหอม กะทิสด", "folder_kw": "กะทิ", "badge": "🔥 ขายดีที่สุด", "out_of_stock": False},
    {"id": 2,  "name": "ไอศครีมรวมมิตร ขนุนเพชรราชา & เพชรดำรง", "folder_kw": "รวมมิตร", "badge": "", "out_of_stock": False},
    {"id": 3,  "name": "ไอศครีมเผือก หอม", "folder_kw": "เผือก", "badge": "", "out_of_stock": False},
    {"id": 4,  "name": "ไอศครีมถั่วดำ", "folder_kw": "ถั่วดำ", "badge": "", "out_of_stock": False},
    {"id": 5,  "name": "ไอศครีมโกโก้", "folder_kw": "โกโก้", "badge": "", "out_of_stock": False},
    {"id": 6,  "name": "ไอศครีมโอริโอ้", "folder_kw": "โอริโอ้", "badge": "", "out_of_stock": False},
    {"id": 7,  "name": "ไอศครีมชาไทย", "folder_kw": "ชาไทย", "badge": "", "out_of_stock": False},
    {"id": 8,  "name": "ไอศครีมชาเขียว", "folder_kw": "ชาเขียว", "badge": "", "out_of_stock": False},
    {"id": 9,  "name": "ไอศครีมไมโล", "folder_kw": "ไมโล", "badge": "", "out_of_stock": False},
    {"id": 10, "name": "ไอศครีมโอวัลตินคุ๊กกี้", "folder_kw": "โอวันติน", "badge": "", "out_of_stock": False},
    {"id": 11, "name": "ไอศครีมบลูเบอรี่", "folder_kw": "บลูเบอรี่", "badge": "", "out_of_stock": False},
    {"id": 12, "name": "ไอศครีมยาคูลท์ปีโป้", "folder_kw": "ยาคลูปีโป้", "badge": "", "out_of_stock": False},
    {"id": 13, "name": "ไอศครีมเปเปอร์มิ้น ช็อคชิพ", "folder_kw": "เปเปอร์มิ้น", "badge": "", "out_of_stock": False},
    {"id": 14, "name": "ไอศครีมนมสด", "folder_kw": "นมสด", "badge": "", "out_of_stock": False},
    {"id": 15, "name": "ไอศครีมวนิลา", "folder_kw": "วนิลา", "badge": "", "out_of_stock": False},
    {"id": 16, "name": "ไอศครีมชาโฮจิฉะ", "folder_kw": "โฮจิชะ", "badge": "", "out_of_stock": False},
    {"id": 17, "name": "ไอศครีมกาแฟ", "folder_kw": "กาแฟ", "badge": "", "out_of_stock": False},
    {"id": 18, "name": "ไอศครีมมะนาวน้ำผึ้ง", "folder_kw": "มะนาวน้ำผึ้ง", "badge": "", "out_of_stock": False},
    {"id": 19, "name": "ไอศครีมส้ม", "folder_kw": "019", "badge": "", "out_of_stock": False},
    {"id": 20, "name": "ไอศครีมบ๊วยโฮชิ", "folder_kw": "บ๊วยโฮชิ", "badge": "", "out_of_stock": False},
    {"id": 21, "name": "ไอศครีมทับทิม", "folder_kw": "ทับทิม", "badge": "", "out_of_stock": False},
    {"id": 22, "name": "ไอศครีมองุ่นสด", "folder_kw": "องุ่นสด", "badge": "", "out_of_stock": False},
    {"id": 23, "name": "ไอศครีมฝรั่ง คลุก บ๊วย", "folder_kw": "ฝรั่ง", "badge": "", "out_of_stock": False},
    {"id": 24, "name": "ไอศครีมมัลเบอรี่ สด", "folder_kw": "มัลเบอรี่", "badge": "", "out_of_stock": False},
    {"id": 25, "name": "ไอศครีมสตรอเบอรี่ สด", "folder_kw": "สตรอเบอรี่", "badge": "", "out_of_stock": True},
    {"id": 26, "name": "ไอศครีมมะม่วง สด", "folder_kw": "มะม่วง", "badge": "", "out_of_stock": True},
    {"id": 27, "name": "ไอศครีมลิ้นจี่ สด", "folder_kw": "ลิ้นจี่", "badge": "", "out_of_stock": True},
    {"id": 28, "name": "ไอศครีมร็อคกี้โร้ด", "folder_kw": "ร็อกกี้โร้ด", "badge": "⭐ รสพิเศษ", "out_of_stock": False},
    {"id": 29, "name": "ไอศครีมนูเทลล่า บราวนี่", "folder_kw": "นูเทลล่า", "badge": "⭐ รสพิเศษ", "out_of_stock": False},
    {"id": 30, "name": "ไอศครีมแมคคาเดเมีย คาราเมล บิสกิต", "folder_kw": "คาราเมล", "badge": "⭐ รสพิเศษ", "out_of_stock": False},
]


FLAVOR_EXACT_ASSET_MAP = {
    1:  ("Screenshot_20250519_000554_Dropbox.jpg", "001. 🍦 กะทิ/1159284.jpg", (0.10, 0.14, 0.90, 0.88)),
    2:  ("Screenshot_20250519_000420_Dropbox.jpg", "002. 🍦 รวมมิตร/1159223.jpg", (0.04, 0.28, 0.56, 0.72)),
    3:  ("Screenshot_20250519_000428_Dropbox.jpg", "002. 🍦 เผือก/1165230.jpg", (0.04, 0.08, 0.96, 0.77)),
    4:  ("Screenshot_20250519_000559_Dropbox.jpg", "003. 🍦 ถั่วดำ/S__6717536.jpg", (0.10, 0.10, 0.90, 0.90)),
    5:  ("Screenshot_20250519_000712_Gallery.jpg", "004. 🍦 โกโก้/1159249.jpg", (0.10, 0.14, 0.90, 0.88)),
    6:  ("Screenshot_20250519_000438_Dropbox.jpg", "005. 🍦 โอริโอ้/1159246.jpg", (0.08, 0.25, 0.92, 0.88)),
    7:  ("Screenshot_20250519_000747_Gallery.jpg", "007. 🍦 ชาไทย/007_ชาไทย_cup_recovered.jpg", None),
    8:  ("Screenshot_20250519_000432_Dropbox.jpg", "006. 🍦 ชาเขียว/006_ชาเขียว_cup_recovered.jpg", None),
    9:  ("Screenshot_20250519_000446_Dropbox.jpg", "008. 🍦 ไมโล/008_ไมโล_cup_recovered.jpg", None),
    10: ("Screenshot_20250519_001932_Gallery.jpg", "009. 🍦 โอวันตินคุ๊กกี้/S__6717484.jpg", (0.08, 0.12, 0.92, 0.90)),
    11: ("Screenshot_20250519_001232_Gallery.jpg", "014. 🍦 บลูเบอรี่/1159210.jpg", (0.04, 0.15, 0.96, 0.58)),
    12: ("Screenshot_20250519_000455_Dropbox.jpg", "016. 🍦 ยาคลูปีโป้/1159204.jpg", (0.10, 0.16, 0.90, 0.90)),
    13: ("Screenshot_20250519_001614_Gallery.jpg", "012. 🍦 เปเปอร์มิ้น ช็อคชิพ/1159278.jpg", (0.10, 0.14, 0.90, 0.90)),
    14: ("Screenshot_20250519_000459_Dropbox.jpg", "011. 🍦 นมสด/1159237.jpg", (0.10, 0.14, 0.90, 0.90)),
    15: ("Screenshot_20250519_001636_Gallery.jpg", "010. 🍦 วนิลา/1159235.jpg", (0.10, 0.14, 0.90, 0.90)),
    16: ("Screenshot_20250519_000520_Dropbox.jpg", "013. 🍦 โฮจิชะ/S__6717474.jpg", (0.10, 0.14, 0.90, 0.90)),
    17: ("Screenshot_20250519_000843_Gallery.jpg", "015. 🍦 กาแฟ/015_กาแฟนมสด_cup_recovered.jpg", None),
    18: ("Screenshot_20250519_000549_Dropbox.jpg", "020. 🍦 มะนาวน้ำผึ้ง/1159264.jpg", (0.10, 0.18, 0.90, 0.92)),
    19: ("Screenshot_20250519_000450_Dropbox.jpg", "019. 🍦 ส้ม/019_ส้มสด_cup_recovered.jpg", None),
    20: ("Screenshot_20250519_000530_Dropbox.jpg", "023. 🍦 บ๊วยโฮชิ/S__6717463.jpg", (0.07, 0.19, 0.93, 0.84)),
    21: ("Screenshot_20250519_001548_Gallery.jpg", "022. 🍦 ทับทิม/S__6717527.jpg", (0.10, 0.16, 0.90, 0.92)),
    22: ("Screenshot_20250519_000525_Dropbox.jpg", "024. 🍦 องุ่นสด/1159268.jpg", (0.10, 0.16, 0.90, 0.92)),
    23: ("1788309824831.jpg",                      "018. 🍦 ฝรั่งสด/018_ฝรั่งสด_cup_recovered.jpg", (0.10, 0.18, 0.90, 0.92)),
    24: ("Screenshot_20250519_000540_Dropbox.jpg", "021. 🍦 มัลเบอรี่/S__6717511.jpg", (0.10, 0.14, 0.90, 0.90)),
    25: ("Screenshot_20250519_001146_Gallery.jpg", "017. 🍦 สตรอเบอรี่/1159251.jpg", (0.10, 0.14, 0.90, 0.90)),
    26: ("Screenshot_20250519_000544_Dropbox.jpg", "026. 🍦 มะม่วง/026_มะม่วงสด_cup_recovered.jpg", None),
    27: ("Screenshot_20250519_001300_Gallery.jpg", "027. 🍦 ลิ้นจี่/027_ลิ้นจี่สด_cup_recovered.jpg", None),
    28: ("Screenshot_20250519_001752_Gallery.jpg", "030. 🍦 ร็อกกี้โร้ด/S__6717467.jpg", (0.10, 0.14, 0.90, 0.90)),
    29: ("Screenshot_20250519_001443_Gallery.jpg", "030. 🍦 นูเทลล่า บราวนี้/S__6717498.jpg", (0.10, 0.14, 0.90, 0.90)),
    30: ("1761984007894.jpg",                      "031. 🍦 คาราเมล แมคคาเดเมีย บิสกิต/S__6717445.jpg", (0.08, 0.14, 0.92, 0.88)),
}


def scan_and_load_flavors_config(force_rescan: bool = False) -> dict:
    r"""
    เชื่อมโยงข้อมูลรูปภาพจากโฟลเดอร์ F:\DAY_ICECREAM_BRANCH_APP\รสชาติทั้งหมด และ
    F:\DAY_ICECREAM_BRANCH_APP\ข้อมูล ถ้วยไอศครีมแบบถ้วยบรรจุสำเร็จ 5oz + ป้ายทั้งหมดของเก่า
    เพื่อให้ทั้ง 30 รสชาติมีทั้งป้ายสติกเกอร์วงกลมพื้นขาวล้วน (sticker_XX.jpg),
    ถ้วยจริง 5 ออนซ์ (cup5oz_XX.jpg — ไม่มีถ้วยไพนต์ 16oz สีแดงหรือถังปั่นปน)
    และภาพคู่สติกเกอร์+ถ้วยจริง 5oz (combo_XX.jpg)
    """
    APP_DIR.mkdir(parents=True, exist_ok=True)
    FLAVORS_IMG_DIR.mkdir(parents=True, exist_ok=True)

    header_logo_cache = ASSETS_DIR / "header_logo_dayicecream.jpg"
    banner_cache = ASSETS_DIR / "quality_banner_2565.jpg"
    if F_DRIVE_MAIN_LOGO.exists() and (force_rescan or not header_logo_cache.exists()):
        im = Image.open(F_DRIVE_MAIN_LOGO).convert("RGB")
        im.thumbnail((600, 600), Image.Resampling.LANCZOS)
        im.save(header_logo_cache, format="JPEG", quality=90)
    if F_DRIVE_QUALITY_BANNER.exists() and (force_rescan or not banner_cache.exists()):
        im = Image.open(F_DRIVE_QUALITY_BANNER).convert("RGB")
        im.thumbnail((1400, 1400), Image.Resampling.LANCZOS)
        im.save(banner_cache, format="JPEG", quality=90)

    local_5oz_root = APP_DIR / "ข้อมูล ถ้วยไอศครีมแบบถ้วยบรรจุสำเร็จ 5oz + ป้ายทั้งหมดของเก่า"
    active_5oz_root = local_5oz_root if local_5oz_root.exists() else F_DRIVE_5OZ_ROOT

    if FLAVORS_CONFIG_PATH.exists() and not force_rescan:
        try:
            saved = json.loads(FLAVORS_CONFIG_PATH.read_text(encoding="utf-8"))
            if isinstance(saved, dict) and len(saved.get("flavors", [])) == 30:
                for f_item in saved["flavors"]:
                    fid = f_item.get("id", 0)
                    if fid in FLAVOR_EXACT_ASSET_MAP:
                        _, cup_rel, _ = FLAVOR_EXACT_ASSET_MAP[fid]
                        f_item["source_image"] = str(active_5oz_root / Path(cup_rel))
                    f_item["sticker_image"] = str(FLAVORS_IMG_DIR / f"sticker_{fid:02d}.jpg")
                    f_item["cup_image"] = str(FLAVORS_IMG_DIR / f"cup5oz_{fid:02d}.jpg")
                    f_item["combo_image"] = str(FLAVORS_IMG_DIR / f"combo_{fid:02d}.jpg")
                    f_item["thumb_image"] = f_item["combo_image"]
                return saved
        except Exception:
            pass

    all_flavors_dir = APP_DIR / "รสชาติทั้งหมด"
    local_5oz_root = APP_DIR / "ข้อมูล ถ้วยไอศครีมแบบถ้วยบรรจุสำเร็จ 5oz + ป้ายทั้งหมดของเก่า"
    active_5oz_root = local_5oz_root if local_5oz_root.exists() else F_DRIVE_5OZ_ROOT

    flavors_list = []
    for base_item in INITIAL_30_FLAVORS:
        item = dict(base_item)
        fid = item["id"]
        st_out = FLAVORS_IMG_DIR / f"sticker_{fid:02d}.jpg"
        cup_out = FLAVORS_IMG_DIR / f"cup5oz_{fid:02d}.jpg"
        combo_out = FLAVORS_IMG_DIR / f"combo_{fid:02d}.jpg"

        if fid in FLAVOR_EXACT_ASSET_MAP:
            st_fname, cup_rel, _ = FLAVOR_EXACT_ASSET_MAP[fid]
            item["sticker_source"] = str(all_flavors_dir / st_fname)
            item["source_image"] = str(active_5oz_root / cup_rel)

        item["sticker_image"] = str(st_out)
        item["cup_image"] = str(cup_out)
        item["combo_image"] = str(combo_out)
        item["thumb_image"] = str(combo_out) if combo_out.exists() else str(FLAVORS_IMG_DIR / f"flavor_{fid:02d}.jpg")
        flavors_list.append(item)

    cfg = {
        "updated_at": time.strftime("%Y-%m-%d %H:%M:%S"),
        "source_folder": str(active_5oz_root),
        "flavors": flavors_list,
    }
    FLAVORS_CONFIG_PATH.write_text(
        json.dumps(cfg, ensure_ascii=False, indent=2), encoding="utf-8"
    )
    return cfg


def save_flavors_config(cfg: dict) -> None:
    cfg["updated_at"] = time.strftime("%Y-%m-%d %H:%M:%S")
    FLAVORS_CONFIG_PATH.write_text(
        json.dumps(cfg, ensure_ascii=False, indent=2), encoding="utf-8"
    )


# ==============================================================================
# PROMO GALLERY MANAGER (F:\DAY_ICECREAM_BRANCH_APP\promo_gallery)
# ==============================================================================
DEFAULT_PROMO_GALLERY_ITEMS = [
    {
        "id": "promo_001",
        "filename": "ป้ายโฆษณา 001.jpg",
        "badge": "🥥 วัตถุดิบธรรมชาติ 100%",
        "title": "1) ความสุขที่คุณสัมผัสได้ — มะพร้าวน้ำหอมบ้านแพ้ว & กะทิทับสะแกคั้นสด",
        "subtitle": "มะพร้าวน้ำหอมพันธุ์หอมใบเตยบ้านแพ้ว 100% & กะทิทับสะแกแท้ 100% คั้นสดวันต่อวัน • ไม่ผสมน้ำเปล่า ไม่มีหางกะทิ ไม่มีน้ำมันพืช ไม่มีนมผง ไร้สารกันบูด/อิมัลซิไฟเออร์",
    },
    {
        "id": "promo_002",
        "filename": "ป้ายโฆษณา 002.jpg",
        "badge": "⭐ MICHELIN GUIDE & BIB GOURMAND",
        "title": "2) มาตรฐานระดับโลก ที่ร้านมิชลินทั่วไทยไว้วางใจกว่า 10 สาขา",
        "subtitle": "เสิร์ฟประจำในร้านอาหารระดับ Michelin Guide & Bib Gourmand กว่า 10 สาขา (ร้านในเหมือง เขาหลัก 8 ปีซ้อน, ภัตตาคารเจี่ยท้งเฮง 6 ปีซ้อน, ครัวลุงลอยป่าลั่น 5 ปีซ้อน, บ้านริมบึง 5 ปีซ้อน, ร้านเปลว 3 ปีซ้อน ฯลฯ) และร้านชั้นนำกว่า 300 ร้านค้า",
    },
    {
        "id": "promo_003",
        "filename": "ป้ายโฆษณา 003.jpg",
        "badge": "🤝 แฟรนไชส์เดียวในโลก คืนมัดจำ 100%",
        "title": "3) ประโยชน์ของการเปิดแฟรนไชส์ Day Ice Cream 6 ข้อ",
        "subtitle": "เปิดแล้วกำไร 100% (ฟรีถ้วย ช้อน โคน ถั่วลิสง) • ไม่มีทางขาดทุน คืนค่ามัดจำตู้ 100% ตลอด 10 ปี • แถมไอติมขายกำไรฟรีตอนเปิด 5,000–10,000 บาท • ไอศกรีมอยู่ได้ 4 เดือน เปลี่ยนใหม่ให้ฟรี!",
    },
    {
        "id": "promo_004",
        "filename": "ป้ายโฆษณา 004.jpg",
        "badge": "🍨 100% ORGANIC HOMEMADE",
        "title": "4) เมนูไอศกรีมโฮมเมดพรีเมียม 100% Organic (Have a nice day)",
        "subtitle": "นมโคสดแท้ 100% • ครีมแท้จากประเทศนิวซีแลนด์ • กะทิแท้ 100% • น้ำมะพร้าวน้ำหอมแท้ 100% • ผลิตสดใหม่วันต่อวัน ส่งความสุขให้คุณทุกวัน",
    },
    {
        "id": "promo_005",
        "filename": "ป้ายโฆษณา 005.jpg",
        "badge": "📱 TIKTOK @dayicecream (120K ผู้ติดตาม)",
        "title": "5) ช่อง TikTok Official (@dayicecream) — ผู้ติดตามกว่า 120,000 คน",
        "subtitle": "ฐานแฟนคลับและลูกค้าประจำทั่วประเทศ • กดถูกใจกว่า 918.6K ครั้ง • อัปเดตขั้นตอนการผลิตไอศกรีมโฮมเมดแท้และรีวิวยอดขายจริงทุกวัน",
    },
    {
        "id": "promo_006",
        "filename": "ป้ายโฆษณา 006.jpg",
        "badge": "🔥 ยอดวิวทะลุ 12,182,966 วิว!",
        "title": "6) กระแสตอบรับถล่มทลายบน TikTok — ยอดวิวทะลุ 12.18 ล้านวิว!",
        "subtitle": "ยอดเข้าชมวิดีโอ 12,182,966 ครั้ง • เข้าถึงผู้ชมกว่า 11,742,647 คน • ยอดเข้าชมโปรไฟล์ 81,369 ครั้ง (เติบโต >999.99%)",
    },
]


def ensure_and_load_promo_gallery(force_reset: bool = False) -> dict:
    r"""
    สร้างโฟลเดอร์ F:\DAY_ICECREAM_BRANCH_APP\promo_gallery และคัดลอกภาพโปรโมตทั้ง 6 ภาพ
    (ป้ายโฆษณา 001.jpg - 006.jpg) เข้าโฟลเดอร์อัตโนมัติ พร้อมโหลด/บันทึกข้อมูลลง promo_gallery_config.json
    """
    PROMO_GALLERY_DIR.mkdir(parents=True, exist_ok=True)

    for item in DEFAULT_PROMO_GALLERY_ITEMS:
        fname = item["filename"]
        src_in_app = APP_DIR / fname
        dst_in_gal = PROMO_GALLERY_DIR / fname
        if src_in_app.exists() and (force_reset or not dst_in_gal.exists()):
            try:
                shutil.copy2(src_in_app, dst_in_gal)
            except Exception:
                pass

    if PROMO_GALLERY_CONFIG_PATH.exists() and not force_reset:
        try:
            cfg = json.loads(PROMO_GALLERY_CONFIG_PATH.read_text(encoding="utf-8"))
            if isinstance(cfg, dict) and isinstance(cfg.get("items"), list) and cfg["items"]:
                cfg["items"] = [
                    it
                    for it in cfg["items"]
                    if not str(it.get("filename", "")).lower().startswith("slide_")
                ]
                known_files = {it.get("filename") for it in cfg["items"]}
                for img_p in sorted(PROMO_GALLERY_DIR.glob("*.*")):
                    if (
                        img_p.suffix.lower() in (".jpg", ".jpeg", ".png", ".webp")
                        and not img_p.name.lower().startswith("slide_")
                        and img_p.name not in known_files
                    ):
                        cfg["items"].append(
                            {
                                "id": f"promo_{int(time.time())}_{len(cfg['items'])+1}",
                                "filename": img_p.name,
                                "badge": "🌟 ภาพโปรโมตเดย์ไอศครีม",
                                "title": img_p.stem,
                                "subtitle": "มาตรฐานไอศกรีมโฮมเมดพรีเมียม เดย์ ไอศกรีม (Day Ice Cream)",
                            }
                        )
                return cfg
        except Exception:
            pass

    cfg = {
        "updated_at": time.strftime("%Y-%m-%d %H:%M:%S"),
        "items": [dict(x) for x in DEFAULT_PROMO_GALLERY_ITEMS],
    }
    PROMO_GALLERY_CONFIG_PATH.write_text(
        json.dumps(cfg, ensure_ascii=False, indent=2), encoding="utf-8"
    )
    return cfg


def save_promo_gallery_config(cfg: dict) -> None:
    cfg["updated_at"] = time.strftime("%Y-%m-%d %H:%M:%S")
    PROMO_GALLERY_CONFIG_PATH.write_text(
        json.dumps(cfg, ensure_ascii=False, indent=2), encoding="utf-8"
    )


VIRAL_VIDEOS_CONFIG_PATH = APP_DIR / "viral_videos_config.json"
VDO_MAIN_DIR = APP_DIR / "vdo"
VIRAL_NEWS_DIR = APP_DIR / "vdo นักข่าวโลกตะลึง"


def resolve_playable_video_path(path_or_url: str, slot_num: int = 1) -> str:
    """
    ตรวจสอบพาธวิดีโอ: หากผู้ใช้เลือกไฟล์ต้นฉบับขนาดใหญ่เกิน 180 MB (เช่น 298 MB หรือ 3.3 GB 4K)
    จะสลับไปใช้ไฟล์ Web HD (720p H.264 +faststart) ของคลิปเดียวกันโดยอัตโนมัติ เพื่อให้เล่นผ่าน st.video()
    บนมือถือและคอมพิวเตอร์ได้ทันทีโดยไม่ติดลิมิต MessageSizeError ของ Streamlit
    """
    s = (path_or_url or "").strip()
    if not s:
        return ""
    if s.startswith("http://") or s.startswith("https://"):
        return s
    p = Path(s)
    if not p.is_absolute():
        p = APP_DIR / p
    if not p.exists():
        fallback = (
            PROMO_GALLERY_DIR / "video_1_viral_news.mp4"
            if slot_num == 1
            else PROMO_GALLERY_DIR / "video_2_sincere_icecream.mp4"
        )
        return str(fallback) if fallback.exists() else ""
    try:
        sz_mb = p.stat().st_size / (1024 * 1024)
        if sz_mb > 180:
            if "นักข่าว" in p.name or "20251222" in p.name or slot_num == 1:
                web_v1 = PROMO_GALLERY_DIR / "video_1_viral_news.mp4"
                if web_v1.exists():
                    return str(web_v1)
            if "จริงใจ" in p.name or slot_num == 2:
                web_v2 = PROMO_GALLERY_DIR / "video_2_sincere_icecream.mp4"
                if web_v2.exists():
                    return str(web_v2)
    except Exception:
        pass
    return str(p)


def discover_available_mp4_files() -> list[dict]:
    """ค้นหาไฟล์ .mp4 ในโฟลเดอร์ F:\\DAY_ICECREAM_BRANCH_APP\\vdo และในเครื่องเพื่อให้เลือกสลับได้ทันที"""
    candidates = []
    seen = set()

    def _add(p: Path, label: str) -> None:
        try:
            if p.exists() and p.is_file() and p.stat().st_size > 0:
                rp = str(p.resolve())
                if rp not in seen:
                    seen.add(rp)
                    sz_mb = p.stat().st_size / (1024 * 1024)
                    candidates.append(
                        {
                            "path": str(p),
                            "label": f"{label} ({p.name} • {sz_mb:.1f} MB)",
                        }
                    )
        except Exception:
            pass

    _add(
        PROMO_GALLERY_DIR / "video_1_viral_news.mp4",
        "⚡ [วิดีโอที่ 1 • Full HD 1080p Web-Optimized โหลดไว 1 วิ] ข่าวด่วน! ทั่วโลกตะลึง! ไอติมไทย",
    )
    _add(
        PROMO_GALLERY_DIR / "video_2_sincere_icecream.mp4",
        "⚡ [วิดีโอที่ 2 • Full HD 1080p Web-Optimized โหลดไว 1 วิ] ไอศกรีมที่จริงใจที่สุด",
    )

    if VDO_MAIN_DIR.exists():
        _add(
            VDO_MAIN_DIR / "นักข่าวโลกตะลึง.mp4",
            "🎥 [วิดีโอที่ 1 • ต้นฉบับในโฟลเดอร์ vdo] นักข่าวโลกตะลึง",
        )
        _add(
            VDO_MAIN_DIR / "ไอศครีมที่จริงใจที่สุด.mp4",
            "🍦 [วิดีโอที่ 2 • ต้นฉบับในโฟลเดอร์ vdo] ไอศครีมที่จริงใจที่สุด",
        )
        for mp4_p in sorted(VDO_MAIN_DIR.glob("*.mp4")):
            _add(mp4_p, "🎬 [โฟลเดอร์ vdo]")

    for sub_d in sorted(APP_DIR.iterdir()):
        if sub_d.is_dir() and sub_d.name not in ("vdo", "cloud_deploy_ready") and (
            "vdo" in sub_d.name.lower()
            or "วิดีโอ" in sub_d.name
            or "จริงใจ" in sub_d.name
            or "นักข่าว" in sub_d.name
        ):
            for mp4_p in sorted(sub_d.glob("*.mp4")):
                _add(mp4_p, f"🎬 [{sub_d.name}]")

    return candidates


def load_viral_videos_config() -> dict:
    PROMO_GALLERY_DIR.mkdir(parents=True, exist_ok=True)
    raw_v1 = VDO_MAIN_DIR / "นักข่าวโลกตะลึง.mp4"
    web_v1 = PROMO_GALLERY_DIR / "video_1_viral_news.mp4"
    default_v1 = web_v1 if web_v1.exists() else raw_v1

    raw_v2 = VDO_MAIN_DIR / "ไอศครีมที่จริงใจที่สุด.mp4"
    web_v2 = PROMO_GALLERY_DIR / "video_2_sincere_icecream.mp4"
    default_v2 = web_v2 if web_v2.exists() else raw_v2

    default_cfg = {
        "updated_at": time.strftime("%Y-%m-%d %H:%M:%S"),
        "video_1": {
            "title": '🔴 วิดีโอไวรัลทะลุล้านวิว: "ข่าวด่วน! ทั่วโลกตะลึง! ไอติมไทย สูตรลับ ไม่พึ่งเคมี แต่อร่อยจนต้องร้องขอชีวิต!"',
            "subtitle": "ต่างชาติยังทึ่ง! ไอศกรีมเมืองไทยเจ้านี้ ไม่ใส่สารขึ้นรูป ไม่พึ่งเคมี แล้วทำไอศกรีมให้อร่อยระดับมิชลินได้ยังไง? • ยอดวิวทะลุล้านวิวบน TikTok @dayicecream",
            "video_path": str(default_v1) if default_v1.exists() else "",
            "raw_source_path": str(raw_v1),
            "external_url": "https://www.tiktok.com/@dayicecream",
            "external_btn_label": "🎵 กดรับชมคลิปเต็มและติดตามบน TikTok @dayicecream (ผู้ติดตาม 120K+ • ยอดวิว 12.18 ล้านวิว!) ↗",
        },
        "video_2": {
            "title": '🍦 วิดีโอพิเศษ: "ไอศกรีมที่จริงใจที่สุด" — เบื้องหลังความตั้งใจของทีมงาน เดย์ ไอศกรีม ส่งความสุขให้คุณทุกวัน',
            "subtitle": "เบื้องหลังความตั้งใจของทีมงานและโรงงาน เดย์ ไอศกรีม คัดสรรวัตถุดิบธรรมชาติแท้ 100% ไร้สารเคมี เพื่อส่งความสุขให้คุณทุกวัน",
            "video_path": str(default_v2) if default_v2.exists() else "",
            "raw_source_path": str(raw_v2),
            "external_url": "https://www.facebook.com/dayicecream",
            "external_btn_label": "📘 กดรับชมบนเพจ Facebook: Dayicecream แฟรนไชส์ไอศครีมที่ดีที่สุด ↗",
        },
    }

    if VIRAL_VIDEOS_CONFIG_PATH.exists():
        try:
            saved = json.loads(VIRAL_VIDEOS_CONFIG_PATH.read_text(encoding="utf-8"))
            if isinstance(saved, dict):
                for k in ("video_1", "video_2"):
                    if isinstance(saved.get(k), dict):
                        default_cfg[k].update(saved[k])
                v1_p = default_cfg["video_1"].get("video_path", "")
                v1_check = Path(v1_p) if Path(v1_p).is_absolute() else (APP_DIR / v1_p)
                if not v1_p or (not v1_p.startswith("http") and not v1_check.exists()):
                    default_cfg["video_1"]["video_path"] = (
                        str(default_v1) if default_v1.exists() else ""
                    )
                v2_p = default_cfg["video_2"].get("video_path", "")
                v2_check = Path(v2_p) if Path(v2_p).is_absolute() else (APP_DIR / v2_p)
                if not v2_p or (not v2_p.startswith("http") and not v2_check.exists()):
                    default_cfg["video_2"]["video_path"] = (
                        str(default_v2) if default_v2.exists() else ""
                    )
                return default_cfg
        except Exception:
            pass

    VIRAL_VIDEOS_CONFIG_PATH.write_text(
        json.dumps(default_cfg, ensure_ascii=False, indent=2), encoding="utf-8"
    )
    return default_cfg


def save_viral_videos_config(cfg: dict) -> None:
    cfg["updated_at"] = time.strftime("%Y-%m-%d %H:%M:%S")
    VIRAL_VIDEOS_CONFIG_PATH.write_text(
        json.dumps(cfg, ensure_ascii=False, indent=2), encoding="utf-8"
    )


# ==============================================================================
# AUTOMATIC LINKTREE SCRAPER & SYNC (https://linktr.ee/Dayicecream)
# ==============================================================================
DEFAULT_LINKS_CONFIG = {
    "source_url": LINKTREE_URL,
    "last_synced": "",
    "profile": {
        "title": "Day Ice Cream",
        "description": "แฟรนไชส์ไอศครีมที่อร่อยที่สุดของคนไทย เปิดแล้วกำไร 100%",
        "avatar_url": "https://ugc.production.linktr.ee/1a4fb0d4-faaa-469d-af05-0b0110ecd3c0_AIdro-mnnXwh8pVEha34lBNOugledbtHMjNs-usle7hlcCxfhEI-s800-c-k-c0x00ffffff-no-rj.jpeg",
    },
    "core_links": {
        "order_promo": {
            "label": "📌 สั่งไอศกรีมออนไลน์ Promotion 22 ถ้วย 990 บาท ส่งฟรีทั่วประเทศไทย",
            "url": "http://m.me/Dayicecream",
            "thumbnail": "https://ugc.production.linktr.ee/6ee2f923-e12a-4ddd-a50d-26c3da9d84de_002----Tiktok.jpeg",
        },
        "franchise_line": {
            "label": "💬 สมัครแฟรนไชส์ ฟรี (LINE Official)",
            "url": "https://line.me/ti/p/BX7Fscqs71",
            "thumbnail": "https://ugc.production.linktr.ee/fe62479b-f2ca-4347-98b5-bc3211076b41_001---.jpeg",
        },
        "website": {
            "label": "🌐 เว็บไซต์หลัก www.dayicecream.com",
            "url": "http://www.dayicecream.com",
            "thumbnail": "https://ugc.production.linktr.ee/07466775-6217-4201-bc87-804e10e305fb_003----.jpeg",
        },
        "google_maps_branches": {
            "label": "📍 แผนที่สาขา 300+ แห่งทั่วไทย",
            "url": GOOGLE_MY_MAPS_VIEWER_URL,
            "thumbnail": "https://ugc.production.linktr.ee/bd0bc3cc-490c-44a4-aa8f-1c4f69ab86fc_005---.png",
        },
        "facebook": {
            "label": "📘 Facebook: ติดตามข่าวสาร แฟรนไชส์เปิดใหม่",
            "url": "https://www.facebook.com/Dayicecream",
            "thumbnail": "https://ugc.production.linktr.ee/d87236f8-a1bd-4cb2-8941-d2c5fc28e274_004----Facebook.png",
        },
        "tiktok": {
            "label": "🎵 TikTok: วิธีผลิตไอศครีม (Update ทุกวัน!)",
            "url": "https://www.tiktok.com/@dayicecream",
            "thumbnail": "https://ugc.production.linktr.ee/fb6b6dd2-99e7-4484-9b7a-799c00e523a8_002----Tiktok.jpeg",
        },
        "youtube": {
            "label": "▶️ YouTube: Day Ice Cream (@dayicecream553)",
            "url": "https://youtube.com/@dayicecream553",
            "thumbnail": "https://ugc.production.linktr.ee/1a4fb0d4-faaa-469d-af05-0b0110ecd3c0_AIdro-mnnXwh8pVEha34lBNOugledbtHMjNs-usle7hlcCxfhEI-s800-c-k-c0x00ffffff-no-rj.jpeg",
        },
    },
    "raw_links": [],
}


def sync_linktree_links(force: bool = False) -> dict:
    APP_DIR.mkdir(parents=True, exist_ok=True)
    if LINKS_CONFIG_PATH.exists() and not force:
        try:
            cached = json.loads(LINKS_CONFIG_PATH.read_text(encoding="utf-8"))
            if cached.get("core_links"):
                return cached
        except Exception:
            pass

    config = json.loads(json.dumps(DEFAULT_LINKS_CONFIG))
    try:
        req = urllib.request.Request(
            LINKTREE_URL,
            headers={
                "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36"
            },
        )
        with urllib.request.urlopen(req, timeout=10) as resp:
            html = resp.read().decode("utf-8", errors="replace")

        match = re.search(
            r'<script id="__NEXT_DATA__"[^>]*>(.*?)</script>', html, re.DOTALL
        )
        if match:
            next_data = json.loads(match.group(1))
            account = next_data.get("props", {}).get("pageProps", {}).get("account", {})
            if account:
                config["profile"]["title"] = account.get(
                    "pageTitle", config["profile"]["title"]
                )
                config["profile"]["description"] = account.get(
                    "description", config["profile"]["description"]
                )
                config["profile"]["avatar_url"] = account.get(
                    "profilePictureUrl", config["profile"]["avatar_url"]
                )

            raw_links = []
            for item in account.get("links", []):
                title = (item.get("title") or "").strip()
                url = (item.get("url") or "").strip()
                thumb = (item.get("modifiers") or {}).get("thumbnailUrl") or ""
                if not url:
                    continue
                raw_links.append({"title": title, "url": url, "thumbnail": thumb})

                t_low = title.lower()
                u_low = url.lower()
                if "m.me/" in u_low or "990" in t_low or "สั่งไอศครีม" in t_low:
                    config["core_links"]["order_promo"] = {
                        "label": f"📌 {title}",
                        "url": url,
                        "thumbnail": thumb or config["core_links"]["order_promo"]["thumbnail"],
                    }
                elif "line.me" in u_low or "สมัครแฟรนไชส์" in t_low:
                    config["core_links"]["franchise_line"] = {
                        "label": f"💬 {title}",
                        "url": url,
                        "thumbnail": thumb or config["core_links"]["franchise_line"]["thumbnail"],
                    }
                elif "dayicecream.com" in u_low:
                    config["core_links"]["website"] = {
                        "label": f"🌐 {title}",
                        "url": url,
                        "thumbnail": thumb or config["core_links"]["website"]["thumbnail"],
                    }
                elif "google.com/maps" in u_low or "สาขา" in t_low:
                    config["core_links"]["google_maps_branches"] = {
                        "label": f"📍 {title}",
                        "url": url,
                        "thumbnail": thumb
                        or config["core_links"]["google_maps_branches"]["thumbnail"],
                    }
                elif "facebook.com" in u_low:
                    config["core_links"]["facebook"] = {
                        "label": f"📘 {title}",
                        "url": url,
                        "thumbnail": thumb or config["core_links"]["facebook"]["thumbnail"],
                    }
                elif "tiktok.com" in u_low:
                    config["core_links"]["tiktok"] = {
                        "label": f"🎵 {title}",
                        "url": url,
                        "thumbnail": thumb or config["core_links"]["tiktok"]["thumbnail"],
                    }
                elif "youtube.com" in u_low or "youtu.be" in u_low:
                    config["core_links"]["youtube"] = {
                        "label": f"▶️ {title}",
                        "url": url,
                        "thumbnail": thumb or config["core_links"]["youtube"]["thumbnail"],
                    }
            config["raw_links"] = raw_links
    except Exception:
        pass

    config["last_synced"] = time.strftime("%Y-%m-%d %H:%M:%S")
    LINKS_CONFIG_PATH.write_text(
        json.dumps(config, ensure_ascii=False, indent=2), encoding="utf-8"
    )
    return config


# ==============================================================================
# DAY STUDIO CHANNELS CONFIG (channels_config.json)
# ==============================================================================
DEFAULT_CHANNELS_CONFIG = {
    "updated_at": "",
    "channels": [
        {
            "id": "day_story",
            "icon": "🎬",
            "name": "DAY STORY",
            "subtitle": "ภาพยนตร์สั้น AI ระดับฮอลลีวูด & เรื่องเล่าแรงบันดาลใจ",
            "description": "ติดตามชมผลงานภาพยนตร์สั้น AI มาตรฐานโรงภาพยนตร์ 35mm และเรื่องราวสร้างแรงบันดาลใจจากสตูดิโอของพี่เดย์",
            "url": "https://www.youtube.com/@DAYSTORY_TH",
            "button_text": "▶️ เข้าชมและกดติดตามช่อง DAY STORY",
            "badge_coming_soon": "⏳ เร็วๆ นี้ (Coming Soon)",
            "accent_color": "#d32f2f",
            "logo_key": "day_story",
        },
        {
            "id": "day_science",
            "icon": "🔬",
            "name": "DAY SCIENCE",
            "subtitle": "วิทยาศาสตร์อาหาร นวัตกรรมความเย็น และความรู้รอบตัวสุดล้ำ",
            "description": "เจาะลึกเบื้องหลังวิทยาศาสตร์ไอศกรีมโฮมเมดแท้ นวัตกรรมการผลิต และสารคดีวิทยาศาสตร์เข้าใจง่าย",
            "url": "",
            "button_text": "▶️ เข้าชมและกดติดตามช่อง DAY SCIENCE",
            "badge_coming_soon": "⏳ เร็วๆ นี้ (Coming Soon)",
            "accent_color": "#0284c7",
            "logo_key": "day_science",
        },
        {
            "id": "day_home_theater",
            "icon": "🍿",
            "name": "DAY HOME THEATER",
            "subtitle": "โรงภาพยนตร์ส่วนตัว ระบบเสียงและภาพระดับมาสเตอร์พีซ",
            "description": "รวมผลงานภาพยนตร์ขนาดยาว รีวิวชุดโฮมเธียเตอร์ และอรรถรสความบันเทิงเต็มรูปแบบสำหรับครอบครัว",
            "url": "",
            "button_text": "▶️ เข้าชมและกดติดตามช่อง DAY HOME THEATER",
            "badge_coming_soon": "⏳ เร็วๆ นี้ (Coming Soon)",
            "accent_color": "#d97706",
            "logo_key": "day_home_theater",
        },
    ],
}


def load_channels_config() -> dict:
    APP_DIR.mkdir(parents=True, exist_ok=True)
    if CHANNELS_CONFIG_PATH.exists():
        try:
            data = json.loads(CHANNELS_CONFIG_PATH.read_text(encoding="utf-8"))
            if isinstance(data, dict) and isinstance(data.get("channels"), list):
                return data
        except Exception:
            pass
    cfg = json.loads(json.dumps(DEFAULT_CHANNELS_CONFIG))
    cfg["updated_at"] = time.strftime("%Y-%m-%d %H:%M:%S")
    CHANNELS_CONFIG_PATH.write_text(
        json.dumps(cfg, ensure_ascii=False, indent=2), encoding="utf-8"
    )
    return cfg


def save_channels_config(cfg: dict) -> None:
    cfg["updated_at"] = time.strftime("%Y-%m-%d %H:%M:%S")
    CHANNELS_CONFIG_PATH.write_text(
        json.dumps(cfg, ensure_ascii=False, indent=2), encoding="utf-8"
    )


# ==============================================================================
# BRANCH DATA LOADER (300+ BRANCHES NATIONWIDE)
# ==============================================================================
def clean_html_text(raw: str) -> str:
    if not raw:
        return ""
    txt = re.sub(r"<br\s*/?>", "\n", raw, flags=re.IGNORECASE)
    txt = re.sub(r"<[^>]+>", "", txt)
    lines = [line.strip() for line in txt.splitlines() if line.strip()]
    return "\n".join(lines)


def extract_phone_numbers(text: str) -> list[str]:
    if not text:
        return []
    matches = re.findall(r"0\d{1,2}[-\s]?\d{3}[-\s]?\d{3,4}", text)
    cleaned = []
    for m in matches:
        norm = re.sub(r"\s+", "-", m.strip())
        if norm not in cleaned:
            cleaned.append(norm)
    return cleaned


def is_internal_pin(name: str, description: str) -> tuple[bool, list[str]]:
    combined = f"{name} {description}"
    matched = [kw for kw in INTERNAL_STATUS_KEYWORDS if kw in combined]
    return (len(matched) > 0), matched


def parse_kml_bytes(raw_bytes: bytes) -> list[dict]:
    if raw_bytes[:2] == b"PK":
        with zipfile.ZipFile(io.BytesIO(raw_bytes)) as zf:
            kml_names = [n for n in zf.namelist() if n.lower().endswith(".kml")]
            xml_bytes = zf.read(kml_names[0]) if kml_names else b""
    else:
        xml_bytes = raw_bytes

    root = ET.fromstring(xml_bytes)
    ns = {"kml": "http://www.opengis.net/kml/2.2"}
    placemarks = root.findall(".//kml:Placemark", ns)

    branches = []
    for idx, pm in enumerate(placemarks, 1):
        name_el = pm.find("kml:name", ns)
        desc_el = pm.find("kml:description", ns)
        coord_el = pm.find(".//kml:coordinates", ns)
        if coord_el is None or not (coord_el.text or "").strip():
            continue

        raw_name = (name_el.text or "").strip() if name_el is not None else f"สาขา #{idx}"
        name = re.sub(r"\s+", " ", raw_name).strip()
        raw_desc = (desc_el.text or "").strip() if desc_el is not None else ""
        clean_desc = clean_html_text(raw_desc)

        coord_str = coord_el.text.strip().split()[0]
        parts = coord_str.split(",")
        if len(parts) < 2:
            continue
        try:
            lon = float(parts[0])
            lat = float(parts[1])
        except ValueError:
            continue

        internal_flag, matched_kw = is_internal_pin(name, clean_desc)
        phones = extract_phone_numbers(f"{name}\n{clean_desc}")
        nav_url = f"https://www.google.com/maps/dir/?api=1&destination={lat},{lon}&travelmode=driving"
        search_url = f"https://www.google.com/maps/search/?api=1&query={lat},{lon}"

        branches.append(
            {
                "id": idx,
                "name": name,
                "description": clean_desc,
                "lat": lat,
                "lon": lon,
                "phones": phones,
                "is_internal": internal_flag,
                "internal_tags": matched_kw,
                "nav_url": nav_url,
                "search_url": search_url,
            }
        )
    return branches


def _normalize_branches_maps_urls(branches: list[dict]) -> list[dict]:
    """บังคับให้ทุกสาขาใช้ Google Maps Universal Cross-Platform Link มาตรฐาน 100%"""
    for b in branches:
        try:
            lat = float(b["lat"])
            lon = float(b["lon"])
            b["nav_url"] = (
                f"https://www.google.com/maps/dir/?api=1&destination={lat},{lon}&travelmode=driving"
            )
            b["search_url"] = (
                f"https://www.google.com/maps/search/?api=1&query={lat},{lon}"
            )
        except Exception:
            pass
    return branches


@st.cache_data(ttl=1800, max_entries=2, show_spinner=False)
def load_branches_live(force_refresh: bool = False) -> tuple[list[dict], str]:
    APP_DIR.mkdir(parents=True, exist_ok=True)
    if not force_refresh and BRANCHES_CACHE_PATH.exists():
        try:
            cached = json.loads(BRANCHES_CACHE_PATH.read_text(encoding="utf-8"))
            cached_branches = _normalize_branches_maps_urls(cached.get("branches", []))
            if cached_branches:
                return (
                    cached_branches,
                    f"ข้อมูลล่าสุด ({cached.get('synced_at', '-')})",
                )
        except Exception:
            pass

    try:
        req = urllib.request.Request(
            GOOGLE_MY_MAPS_KML_URL,
            headers={"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)"},
        )
        with urllib.request.urlopen(req, timeout=10) as resp:
            raw_bytes = resp.read()
        branches = _normalize_branches_maps_urls(parse_kml_bytes(raw_bytes))
        if branches:
            BRANCHES_CACHE_PATH.write_text(
                json.dumps(
                    {
                        "synced_at": time.strftime("%Y-%m-%d %H:%M:%S"),
                        "branches": branches,
                    },
                    ensure_ascii=False,
                    indent=2,
                ),
                encoding="utf-8",
            )
            return branches, f"อัปเดตล่าสุด ({time.strftime('%H:%M:%S')})"
    except Exception:
        pass

    if BRANCHES_CACHE_PATH.exists():
        try:
            cached = json.loads(BRANCHES_CACHE_PATH.read_text(encoding="utf-8"))
            return (
                _normalize_branches_maps_urls(cached.get("branches", [])),
                f"ข้อมูลล่าสุด ({cached.get('synced_at', '-')})",
            )
        except Exception:
            pass
    return [], "ไม่พบข้อมูลสาขา"


def haversine_km(lat1: float, lon1: float, lat2: float, lon2: float) -> float:
    r = 6371.0
    dlat = math.radians(lat2 - lat1)
    dlon = math.radians(lon2 - lon1)
    a = (
        math.sin(dlat / 2) ** 2
        + math.cos(math.radians(lat1))
        * math.cos(math.radians(lat2))
        * math.sin(dlon / 2) ** 2
    )
    return 2 * r * math.asin(math.sqrt(a))


def detect_approx_location_ip() -> tuple[float, float, str]:
    try:
        req = urllib.request.Request(
            "http://ip-api.com/json/?fields=status,country,regionName,city,lat,lon",
            headers={"User-Agent": "Mozilla/5.0"},
        )
        with urllib.request.urlopen(req, timeout=3) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        if (
            data.get("status") == "success"
            and data.get("country") in ("Thailand", "TH")
            and data.get("lat")
            and data.get("lon")
        ):
            city = data.get("city") or ""
            region = data.get("regionName") or ""
            return (
                float(data["lat"]),
                float(data["lon"]),
                f"{city} {region}".strip() or "ตำแหน่งปัจจุบันของคุณ",
            )
    except Exception:
        pass
    return DEFAULT_HQ_LAT, DEFAULT_HQ_LON, "สำนักงานใหญ่ เดย์ไอศครีม (จ.นครปฐม)"


# ==============================================================================
# THAILAND BRANCH MAP BUILDER (FOCUSED ON THAILAND: [13.75, 100.52], zoom_start=6)
# ==============================================================================
@st.cache_data(ttl=900, max_entries=6, show_spinner=False)
def build_thailand_branch_map(
    branches: list[dict],
    ref_lat: float,
    ref_lon: float,
    gps_active: bool,
    loc_label: str,
    pin_public_uri: str,
    pin_internal_uri: str,
    search_active: bool = False,
) -> str:
    if gps_active:
        center_lat, center_lon = ref_lat, ref_lon
        zoom_start = 11
    elif search_active and branches:
        center_lat = sum(b["lat"] for b in branches) / len(branches)
        center_lon = sum(b["lon"] for b in branches) / len(branches)
        zoom_start = 10 if len(branches) < 25 else 7
    else:
        # โฟกัสเฉพาะประเทศไทยพอดีสวยงามตามสเปก
        center_lat, center_lon = 13.75, 100.52
        zoom_start = 6

    fmap = folium.Map(
        location=[center_lat, center_lon],
        zoom_start=zoom_start,
        tiles="OpenStreetMap",
        control_scale=True,
    )

    fmap.get_root().header.add_child(
        folium.Element(
            f"<script>window.DAY_PIN_URI_JS = {json.dumps(pin_public_uri)}; window.DAY_PIN_INT_URI_JS = {json.dumps(pin_internal_uri or pin_public_uri)};</script>"
        )
    )

    for b in branches:
        is_int = b.get("is_internal", False)
        b_lat = b["lat"]
        b_lon = b["lon"]
        b_nav_url = f"https://www.google.com/maps/dir/?api=1&destination={b_lat},{b_lon}&travelmode=driving"
        b_search_url = f"https://www.google.com/maps/search/?api=1&query={b_lat},{b_lon}"
        status_badge = (
            f'<span style="background:#d32f2f;color:#fff;padding:2px 8px;border-radius:99px;font-size:11px;font-weight:700;">'
            f'สถานะภายใน: {", ".join(b.get("internal_tags", []))}</span>'
            if is_int
            else '<span style="background:#16a34a;color:#fff;padding:2px 8px;border-radius:99px;font-size:11px;font-weight:700;">🍦 เปิดบริการ</span>'
        )
        phones_html = (
            f'<div style="margin-top:6px;font-size:13px;color:#b71c1c;font-weight:700;">📞 โทร: {", ".join(b["phones"])}</div>'
            if b.get("phones")
            else ""
        )
        dist_html = (
            f'<div style="margin-top:4px;font-size:12.5px;color:#d32f2f;font-weight:700;">📏 ห่างจากจุดอ้างอิงประมาณ {b["distance_km"]:.2f} กม.</div>'
            if b.get("distance_km") is not None
            else ""
        )
        desc_text = (b.get("description") or "").replace("\n", "<br>")
        if len(desc_text) > 220:
            desc_text = desc_text[:220] + "..."

        pin_cls = "day-pin-int" if is_int else "day-pin-pub"
        popup_html = f"""
        <div style="font-family:'Prompt','Kanit',sans-serif;min-width:250px;max-width:310px;padding:6px;color:#2B1810;">
            <div style="display:flex;align-items:center;gap:8px;margin-bottom:6px;">
                <span class="day-map-pin-badge {pin_cls}"></span>
                <div>{status_badge}</div>
            </div>
            <div style="font-size:15px;font-weight:800;color:#b71c1c;line-height:1.35;">{b['name']}</div>
            {dist_html}
            {phones_html}
            <div style="margin-top:6px;font-size:12px;color:#5C4033;line-height:1.45;">{desc_text}</div>
            <a href="{b_nav_url}" target="_blank" rel="noopener noreferrer"
               style="display:block;margin-top:10px;text-align:center;background:linear-gradient(135deg,#d32f2f,#ff5252);color:#ffffff;
                      font-weight:800;padding:9px 12px;border-radius:10px;text-decoration:none;font-size:13.5px;box-shadow:0 4px 10px rgba(211,47,47,0.25);">
               🚗 กดนำทางด้วย Google Maps
            </a>
            <a href="{b_search_url}" target="_blank" rel="noopener noreferrer"
               style="display:block;margin-top:6px;text-align:center;background:#fff1f2;color:#b71c1c;border:1.5px solid #fca5a5;
                      font-weight:700;padding:6px 10px;border-radius:8px;text-decoration:none;font-size:12px;">
               📍 ดูหมุดพิกัดบน Google Maps
            </a>
        </div>
        """

        icon_uri = pin_internal_uri if is_int else pin_public_uri
        if icon_uri:
            marker_icon = folium.CustomIcon(
                icon_image=(
                    "data:image/png;base64,__DAY_PIN_INT__"
                    if is_int
                    else "data:image/png;base64,__DAY_PIN_PUB__"
                ),
                icon_size=(40, 40),
                icon_anchor=(20, 20),
                popup_anchor=(0, -18),
            )
        else:
            marker_icon = folium.Icon(color="red", icon="ice-cream", prefix="fa")

        folium.Marker(
            location=[b_lat, b_lon],
            tooltip=f"🍦 {b['name']} ({b.get('distance_km', 0):.1f} กม.)",
            popup=folium.Popup(popup_html, max_width=330),
            icon=marker_icon,
        ).add_to(fmap)

    branches_js_data = json.dumps(
        [
            {
                "name": b["name"],
                "lat": b["lat"],
                "lon": b["lon"],
                "phones": b.get("phones", []),
                "nav_url": f"https://www.google.com/maps/dir/?api=1&destination={b['lat']},{b['lon']}&travelmode=driving",
                "search_url": f"https://www.google.com/maps/search/?api=1&query={b['lat']},{b['lon']}",
            }
            for b in branches
        ],
        ensure_ascii=False,
    )

    map_var = fmap.get_name()
    header_and_gps_overlay = f"""
    <link href="https://fonts.googleapis.com/css2?family=Kanit:wght@400;500;600;700;800&family=Prompt:wght@400;500;600;700;800&display=swap" rel="stylesheet">
    <style>
        .day-map-pin-badge {{
            display: inline-block;
            width: 34px;
            height: 34px;
            flex-shrink: 0;
            background-size: contain;
            background-repeat: no-repeat;
            background-position: center;
        }}
        .day-pin-pub {{
            background-image: url("{pin_public_uri}");
        }}
        .day-pin-int {{
            background-image: url("{pin_internal_uri or pin_public_uri}");
        }}
        .day-map-topbar {{
            font-family: 'Prompt', 'Kanit', sans-serif;
            background: linear-gradient(135deg, #d32f2f 0%, #e53935 55%, #ff5252 100%);
            color: #ffffff;
            padding: 12px 18px;
            border-radius: 16px 16px 0 0;
            border-bottom: 3px solid #fde047;
            display: flex;
            align-items: center;
            justify-content: space-between;
            flex-wrap: wrap;
            gap: 10px;
            box-shadow: 0 6px 18px rgba(211,47,47,0.18);
        }}
        .day-gps-btn {{
            background: #ffffff;
            color: #d32f2f;
            border: 2px solid #fde047;
            padding: 8px 16px;
            border-radius: 999px;
            font-family: 'Prompt', 'Kanit', sans-serif;
            font-weight: 800;
            font-size: 13.5px;
            cursor: pointer;
            box-shadow: 0 4px 12px rgba(0, 0, 0, 0.15);
            transition: all 0.2s ease;
            text-decoration: none;
            display: inline-flex;
            align-items: center;
            gap: 5px;
        }}
        .day-gps-btn:hover {{
            transform: translateY(-1px) scale(1.02);
            background: #fffbeb;
        }}
        #gps-results-bar {{
            display: none;
            font-family: 'Prompt', 'Kanit', sans-serif;
            background: #FFFBF5;
            color: #2B1810;
            padding: 12px 16px;
            border-bottom: 2px solid #fecaca;
        }}
        .gps-nearest-grid {{
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(220px, 1fr));
            gap: 10px;
            margin-top: 8px;
        }}
        .gps-mini-card {{
            background: #ffffff;
            border: 1.5px solid #fca5a5;
            border-radius: 12px;
            padding: 10px 12px;
            box-shadow: 0 4px 10px rgba(211,47,47,0.08);
        }}
    </style>

    <div class="day-map-topbar">
        <div style="display:flex;align-items:center;gap:10px;flex-wrap:wrap;">
            <img src="{pin_public_uri}" style="width:36px;height:36px;border-radius:50%;background:#fff;padding:2px;" />
            <span style="font-weight:800;font-size:16px;color:#ffffff;">
                🗺️ แผนที่สาขา เดย์ไอศครีม ทั่วประเทศไทย
            </span>
            <span style="background:#ffffff;color:#d32f2f;font-weight:800;font-size:12px;padding:3px 11px;border-radius:99px;">
                {"กว่า 300+ สาขาทั่วประเทศไทย" if len(branches) <= 300 else f"{len(branches):,} สาขาทั่วประเทศไทย"}
            </span>
            <span id="gps-status-text" style="font-size:12.5px;color:#fef08a;font-weight:600;">
                (คลิกที่โลโก้เดย์ไอศครีมบนแผนที่เพื่อดูชื่อร้าน เบอร์โทร และกดนำทาง)
            </span>
        </div>
        <div style="display:flex;gap:8px;flex-wrap:wrap;align-items:center;">
            <button type="button" class="day-gps-btn" onclick="locateCustomerGPS()">
                📍 กดค้นหาสาขาใกล้ตำแหน่งฉันตอนนี้ (GPS)
            </button>
            <a href="https://www.google.com/maps/dir/?api=1&destination={branches[0]['lat'] if branches else ref_lat},{branches[0]['lon'] if branches else ref_lon}&travelmode=driving"
               target="_blank" rel="noopener noreferrer"
               class="day-gps-btn" style="background:#fef08a;color:#991b1b;border-color:#ffffff;">
                🚗 เปิดนำทาง Google Maps ทันที ↗
            </a>
        </div>
    </div>
    <div id="gps-results-bar">
        <div id="gps-results-header" style="font-weight:800;color:#d32f2f;font-size:14.5px;"></div>
        <div id="gps-nearest-grid" class="gps-nearest-grid"></div>
    </div>

    <script>
        const ALL_BRANCHES_JS = {branches_js_data};
        const DAY_PIN_URI_JS = window.DAY_PIN_URI_JS;
        let userMarkerLayer = null;
        let lineLayer = null;
        let nearestCircleLayer = null;

        function calcKm(lat1, lon1, lat2, lon2) {{
            const R = 6371.0;
            const dLat = (lat2 - lat1) * Math.PI / 180;
            const dLon = (lon2 - lon1) * Math.PI / 180;
            const a = Math.sin(dLat/2) * Math.sin(dLat/2) +
                      Math.cos(lat1 * Math.PI / 180) * Math.cos(lat2 * Math.PI / 180) *
                      Math.sin(dLon/2) * Math.sin(dLon/2);
            return 2 * R * Math.asin(Math.sqrt(a));
        }}

        document.addEventListener("DOMContentLoaded", function() {{
            const map = {map_var};
            const gpsActiveInit = {str(gps_active).lower()};
            const refLat = {ref_lat};
            const refLon = {ref_lon};

            window.highlightNearestFrom = function(lat, lon, labelText) {{
                if (userMarkerLayer) map.removeLayer(userMarkerLayer);
                if (lineLayer) map.removeLayer(lineLayer);
                if (nearestCircleLayer) map.removeLayer(nearestCircleLayer);

                const searchPinUrl = `https://www.google.com/maps/search/?api=1&query=${{lat}},${{lon}}`;
                userMarkerLayer = L.circleMarker([lat, lon], {{
                    radius: 10,
                    color: '#ffffff',
                    weight: 3,
                    fillColor: '#2563eb',
                    fillOpacity: 1.0
                }}).addTo(map).bindPopup(
                    `<div style="font-family:'Prompt',sans-serif;font-weight:700;color:#1e40af;">📍 ${{labelText}}<br><span style="font-size:12px;color:#475569;">(${{lat.toFixed(5)}}, ${{lon.toFixed(5)}})</span><br><a href="${{searchPinUrl}}" target="_blank" rel="noopener noreferrer" style="display:inline-block;margin-top:6px;background:#2563eb;color:#fff;padding:4px 10px;border-radius:6px;text-decoration:none;font-size:11.5px;">🗺️ เปิดพิกัดนี้ใน Google Maps</a></div>`
                ).openPopup();

                if (!ALL_BRANCHES_JS.length) return;

                const ranked = ALL_BRANCHES_JS.map(b => ({{
                    ...b,
                    live_km: calcKm(lat, lon, b.lat, b.lon)
                }})).sort((a, b) => a.live_km - b.live_km);

                const closest = ranked[0];
                nearestCircleLayer = L.circleMarker([closest.lat, closest.lon], {{
                    radius: 22,
                    color: '#d32f2f',
                    weight: 3,
                    fillColor: '#fde047',
                    fillOpacity: 0.28
                }}).addTo(map);

                lineLayer = L.polyline([[lat, lon], [closest.lat, closest.lon]], {{
                    color: '#d32f2f',
                    weight: 3.5,
                    dashArray: '8, 8'
                }}).addTo(map);

                map.fitBounds([[lat, lon], [closest.lat, closest.lon]], {{ padding: [55, 55], maxZoom: 13 }});

                const bar = document.getElementById('gps-results-bar');
                const header = document.getElementById('gps-results-header');
                const grid = document.getElementById('gps-nearest-grid');
                bar.style.display = 'block';
                header.innerHTML = `🎯 สาขาที่ใกล้คุณที่สุด! (อ้างอิงจาก ${{labelText}})`;

                grid.innerHTML = ranked.slice(0, 4).map((b, i) => `
                    <div class="gps-mini-card">
                        <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:4px;">
                            <span style="background:#d32f2f;color:#ffffff;font-weight:800;font-size:11px;padding:2px 8px;border-radius:99px;">อันดับ #${{i+1}} ใกล้สุด</span>
                            <span style="color:#15803d;font-weight:800;font-size:13px;">📏 ${{b.live_km.toFixed(2)}} กม.</span>
                        </div>
                        <div style="font-weight:700;font-size:13px;color:#2B1810;line-height:1.35;margin:5px 0;">${{b.name}}</div>
                        <a href="https://www.google.com/maps/dir/?api=1&destination=${{b.lat}},${{b.lon}}&travelmode=driving" target="_blank" rel="noopener noreferrer"
                           style="display:block;text-align:center;background:linear-gradient(135deg,#d32f2f,#ff5252);color:#fff;font-weight:800;padding:7px 10px;border-radius:8px;text-decoration:none;font-size:12.5px;margin-top:5px;">
                            🚗 กดนำทางด้วย Google Maps
                        </a>
                    </div>
                `).join('');
            }};

            window.locateCustomerGPS = function() {{
                const statusEl = document.getElementById('gps-status-text');
                statusEl.innerHTML = '<span style="color:#fef08a;">⏳ กำลังค้นหาพิกัด GPS ของคุณ...</span>';
                try {{
                    if (window.parent && typeof window.parent.triggerDayTopGPS === 'function') {{
                        window.parent.triggerDayTopGPS();
                        return;
                    }}
                }} catch (e) {{}}
                const geoObj = (window.parent && window.parent.navigator && window.parent.navigator.geolocation)
                    ? window.parent.navigator.geolocation
                    : navigator.geolocation;
                if (geoObj) {{
                    geoObj.getCurrentPosition(
                        (pos) => {{
                            const lat = pos.coords.latitude;
                            const lon = pos.coords.longitude;
                            statusEl.innerHTML = `<span style="color:#dcfce7;">✅ พบพิกัด GPS ของคุณแล้ว!</span>`;
                            window.highlightNearestFrom(lat, lon, "พิกัด GPS ปัจจุบันของคุณ");
                        }},
                        (err) => {{
                            statusEl.innerHTML = `<span style="color:#fef08a;">📍 แสดงสาขาใกล้จุดอ้างอิงที่เลือกไว้ (กดนำทางได้ทันที)</span>`;
                            window.highlightNearestFrom(refLat, refLon, "{loc_label}");
                        }},
                        {{ enableHighAccuracy: true, timeout: 4500, maximumAge: 60000 }}
                    );
                }} else {{
                    statusEl.innerHTML = `<span style="color:#fef08a;">📍 แสดงสาขาใกล้จุดอ้างอิงที่เลือกไว้ (กดนำทางได้ทันที)</span>`;
                    window.highlightNearestFrom(refLat, refLon, "{loc_label}");
                }}
            }};

            if (gpsActiveInit) {{
                setTimeout(() => {{
                    window.highlightNearestFrom(refLat, refLon, "{loc_label}");
                }}, 250);
            }}
        }});
    </script>
    """
    fmap.get_root().html.add_child(folium.Element(header_and_gps_overlay))
    rendered_html = fmap.get_root().render()
    rendered_html = rendered_html.replace(
        '"data:image/png;base64,__DAY_PIN_PUB__"', "window.DAY_PIN_URI_JS"
    )
    rendered_html = rendered_html.replace(
        '"data:image/png;base64,__DAY_PIN_INT__"', "window.DAY_PIN_INT_URI_JS"
    )
    return rendered_html


VIP_CSV_HEADERS = [
    "วันเวลาสั่งซื้อ",
    "ชื่อผู้รับ",
    "เบอร์โทรศัพท์",
    "ที่อยู่จัดส่ง",
    "รหัสแพ็กเกจ",
    "โปรโมชันที่เลือก",
    "จำนวนถ้วยรวม",
    "ยอดเงินรวม (บาท)",
    "รายการรสชาติที่เลือก",
    "flavors_json",
    "ข้อความสรุปบิลเต็ม",
]


def normalize_phone_digits(phone_raw: str) -> str:
    return re.sub(r"[^0-9]", "", str(phone_raw or ""))


def ensure_vip_csv_files() -> None:
    """สร้างไฟล์ฐานข้อมูลสมาชิก VIP (vip_customers_ orders.csv และ vip_customers_orders.csv) พร้อมหัวตารางภาษาไทย"""
    APP_DIR.mkdir(parents=True, exist_ok=True)
    for csv_path in (VIP_CUSTOMERS_CSV_SPACE_PATH, VIP_CUSTOMERS_CSV_CLEAN_PATH):
        if not csv_path.exists():
            try:
                with open(csv_path, mode="w", encoding="utf-8-sig", newline="") as f:
                    writer = csv.writer(f)
                    writer.writerow(VIP_CSV_HEADERS)
            except Exception:
                pass


def load_vip_customer_orders() -> list[dict]:
    """โหลดประวัติการสั่งซื้อของสมาชิก VIP ทั้งหมดจากไฟล์ CSV ในเครื่อง"""
    ensure_vip_csv_files()
    target_path = (
        VIP_CUSTOMERS_CSV_SPACE_PATH
        if VIP_CUSTOMERS_CSV_SPACE_PATH.exists()
        else VIP_CUSTOMERS_CSV_CLEAN_PATH
    )
    records: list[dict] = []
    if not target_path.exists():
        return records
    try:
        with open(target_path, mode="r", encoding="utf-8-sig", newline="") as f:
            reader = csv.DictReader(f)
            for row in reader:
                if isinstance(row, dict):
                    records.append(row)
    except Exception:
        pass
    return records


def find_latest_vip_order(phone_search: str = "") -> dict | None:
    """ค้นหาข้อมูลที่อยู่และรสชาติโปรดครั้งล่าสุดของสมาชิก VIP (ค้นหาจากเบอร์โทร หรือดึงรายการล่าสุด)"""
    records = load_vip_customer_orders()
    if not records:
        return None
    norm_q = normalize_phone_digits(phone_search)
    if norm_q:
        for row in reversed(records):
            row_phone = normalize_phone_digits(row.get("เบอร์โทรศัพท์", ""))
            if row_phone and (row_phone == norm_q or row_phone.endswith(norm_q) or norm_q.endswith(row_phone)):
                return row
        return None
    for row in reversed(records):
        if (row.get("ชื่อผู้รับ") or "").strip() or (row.get("เบอร์โทรศัพท์") or "").strip():
            return row
    return None


def save_vip_customer_order(
    cust_name: str,
    cust_phone: str,
    cust_address: str,
    pkg_code: str,
    pkg_title: str,
    total_cups: int,
    total_price: int,
    flavors_summary: str,
    flavors_map: dict,
    full_bill_text: str,
    force: bool = False,
) -> bool:
    """
    บันทึกข้อมูลสมาชิก VIP และประวัติการสั่งซื้อลงไฟล์ F:\\DAY_ICECREAM_BRANCH_APP\\vip_customers_ orders.csv
    (และ vip_customers_orders.csv) อัตโนมัติโดยไม่ต้องใช้รหัสผ่าน
    """
    ensure_vip_csv_files()
    name_clean = (cust_name or "").strip()
    phone_clean = (cust_phone or "").strip()
    addr_clean = (cust_address or "").strip()
    if not (name_clean or phone_clean or addr_clean) and not force:
        return False

    flavors_json_str = json.dumps(flavors_map, ensure_ascii=False, sort_keys=True)
    sig = f"{name_clean}|{phone_clean}|{addr_clean}|{pkg_code}|{total_cups}|{total_price}|{flavors_json_str}"
    if not force and st.session_state.get("last_vip_saved_sig") == sig:
        return False

    now_str = time.strftime("%Y-%m-%d %H:%M:%S")
    row_data = [
        now_str,
        name_clean or "(ไม่ระบุชื่อ)",
        phone_clean or "(ไม่ระบุเบอร์โทร)",
        addr_clean or "(ไม่ระบุที่อยู่)",
        pkg_code,
        pkg_title,
        int(total_cups),
        int(total_price),
        flavors_summary,
        flavors_json_str,
        full_bill_text,
    ]
    saved_ok = False
    for csv_path in (VIP_CUSTOMERS_CSV_SPACE_PATH, VIP_CUSTOMERS_CSV_CLEAN_PATH):
        try:
            file_exists = csv_path.exists() and csv_path.stat().st_size > 0
            with open(csv_path, mode="a", encoding="utf-8-sig", newline="") as f:
                writer = csv.writer(f)
                if not file_exists:
                    writer.writerow(VIP_CSV_HEADERS)
                writer.writerow(row_data)
            saved_ok = True
        except Exception:
            pass

    if saved_ok:
        st.session_state["last_vip_saved_sig"] = sig
        try:
            if phone_clean:
                st.query_params["vip_phone"] = phone_clean
            if name_clean:
                st.query_params["vip_name"] = name_clean
        except Exception:
            pass
    return saved_ok


def render_one_click_order_to_chat_buttons(
    order_text: str,
    button_id_suffix: str,
    fb_page_url: str = "https://www.facebook.com/dayicecream",
    vip_payload: dict | None = None,
) -> None:
    """
    แสดงปุ่มกดส่งคำสั่งซื้อขนาดใหญ่ 2 ปุ่มคู่กัน:
    1) 🟢 ส่งบิลสั่งซื้อนี้เข้า LINE: Dayinterfood ทันที (รองรับทั้ง oaMessage/@dayinterfood และคัดลอกเปิดแชท LINE ทันที)
    2) 🔵 คัดลอกบิล & ทักแชทสั่งซื้อทาง Facebook Page (คัดลอกบิลลง Clipboard มือถืออัตโนมัติ + เปิด Facebook Page ทันที)
    พร้อมบันทึกข้อมูลสมาชิก VIP ลง localStorage อัตโนมัติ
    """
    escaped_js_text = json.dumps(order_text, ensure_ascii=False)
    vip_json_js = json.dumps(vip_payload or {}, ensure_ascii=False)
    encoded_bill_text = urllib.parse.quote(order_text, safe="")
    line_oa_msg_url = f"https://line.me/R/oaMessage/@dayinterfood/?{encoded_bill_text}"
    line_direct_friend_url = "https://line.me/ti/p/~Dayinterfood"
    line_qr_short_url = "https://line.me/ti/p/BX7Fscqs71"
    fb_target_url = fb_page_url or "https://www.facebook.com/dayicecream"

    html_block = f"""
    <link href="https://fonts.googleapis.com/css2?family=Kanit:wght@500;600;700;800;900&family=Prompt:wght@500;600;700;800&display=swap" rel="stylesheet">
    <style>
        * {{
            box-sizing: border-box;
            font-family: 'Kanit', 'Prompt', sans-serif;
        }}
        body {{
            margin: 0;
            padding: 2px 0;
            background: transparent;
        }}
        .chat-order-grid {{
            display: grid;
            grid-template-columns: 1fr 1fr;
            gap: 12px;
            width: 100%;
        }}
        .chat-btn {{
            display: flex;
            flex-direction: column;
            align-items: center;
            justify-content: center;
            text-align: center;
            padding: 15px 16px;
            border-radius: 18px;
            text-decoration: none !important;
            color: #ffffff !important;
            font-weight: 800;
            font-size: 16px;
            line-height: 1.3;
            cursor: pointer;
            transition: all 0.18s ease;
            position: relative;
        }}
        .chat-btn:hover {{
            transform: translateY(-2px);
            filter: brightness(1.06);
        }}
        .chat-btn:active {{
            transform: translateY(2px);
        }}
        .chat-btn-line {{
            background: linear-gradient(135deg, #047857 0%, #059669 45%, #10b981 100%);
            border: 2.5px solid #fde047;
            box-shadow: 0 5px 0 #064e3b, 0 10px 22px rgba(5, 150, 105, 0.32);
        }}
        .chat-btn-fb {{
            background: linear-gradient(135deg, #1e3a8a 0%, #1d4ed8 50%, #2563eb 100%);
            border: 2.5px solid #fde047;
            box-shadow: 0 5px 0 #172554, 0 10px 22px rgba(29, 78, 216, 0.32);
        }}
        .chat-btn-sub {{
            font-size: 12px;
            font-weight: 600;
            color: #fef08a;
            margin-top: 4px;
        }}
        .aux-links-row {{
            display: flex;
            justify-content: space-between;
            align-items: center;
            flex-wrap: wrap;
            gap: 8px;
            margin-top: 10px;
            padding: 8px 12px;
            background: #fffbeb;
            border: 1.5px dashed #f59e0b;
            border-radius: 12px;
            font-size: 12.5px;
            color: #78350f;
            font-weight: 700;
        }}
        .aux-links-row a {{
            color: #b91c1c;
            font-weight: 800;
            text-decoration: underline;
        }}
        #copyStatus_{button_id_suffix} {{
            display: none;
            margin-top: 8px;
            padding: 10px 14px;
            border-radius: 12px;
            background: #ecfdf5;
            border: 2px solid #10b981;
            color: #065f46;
            font-size: 13.5px;
            font-weight: 800;
            text-align: center;
        }}
        @media (max-width: 768px) {{
            .chat-order-grid {{
                grid-template-columns: 1fr;
                gap: 10px;
            }}
            .chat-btn {{
                font-size: 15px;
                padding: 13px 14px;
            }}
        }}
    </style>

    <div id="order-buttons-root-{button_id_suffix}">
        <div class="chat-order-grid">
            <a class="chat-btn chat-btn-line"
               href="{line_oa_msg_url}"
               target="_blank"
               rel="noopener noreferrer"
               onclick="copyBillAndSaveVIP_{button_id_suffix}('LINE')">
                <span>🟢 ส่งบิลสั่งซื้อนี้เข้า LINE: Dayinterfood ทันที</span>
                <span class="chat-btn-sub">👆 คัดลอกบิลอัตโนมัติ + เปิดแชท LINE พร้อมส่งใน 1 วินาที ❯</span>
            </a>

            <a class="chat-btn chat-btn-fb"
               href="{fb_target_url}"
               target="_blank"
               rel="noopener noreferrer"
               onclick="copyBillAndSaveVIP_{button_id_suffix}('FB')">
                <span>🔵 คัดลอกบิล & ทักแชทสั่งซื้อทาง Facebook Page</span>
                <span class="chat-btn-sub">👆 คัดลอกบิลลงมือถืออัตโนมัติ + เปิดหน้าแชท Facebook ทันที ❯</span>
            </a>
        </div>

        <div id="copyStatus_{button_id_suffix}"></div>

        <div class="aux-links-row">
            <span>💡 <b>ทางลัดสำรอง:</b> หากแอป LINE ไม่เด้งข้อความอัตโนมัติ บิลถูกคัดลอกไว้แล้ว กดวางส่งได้ที่:</span>
            <div style="display:flex;gap:12px;flex-wrap:wrap;">
                <a href="{line_direct_friend_url}" target="_blank" rel="noopener noreferrer" onclick="copyBillAndSaveVIP_{button_id_suffix}('LINE_ID')">💬 เปิด LINE ID: ~Dayinterfood ↗</a>
                <a href="{line_qr_short_url}" target="_blank" rel="noopener noreferrer" onclick="copyBillAndSaveVIP_{button_id_suffix}('LINE_QR')">📲 ลิงก์ตรง LINE: Dayinterfood ↗</a>
                <a href="tel:0863328091" target="_blank">📞 โทรสั่งด่วน: 086-3328091</a>
            </div>
        </div>
    </div>

    <script>
        function fallbackCopyText_{button_id_suffix}(text) {{
            try {{
                var ta = document.createElement("textarea");
                ta.value = text;
                ta.style.position = "fixed";
                ta.style.left = "-9999px";
                document.body.appendChild(ta);
                ta.focus();
                ta.select();
                document.execCommand("copy");
                document.body.removeChild(ta);
            }} catch (e) {{}}
        }}

        function copyBillAndSaveVIP_{button_id_suffix}(channelName) {{
            var text = {escaped_js_text};
            var vipData = {vip_json_js};
            fallbackCopyText_{button_id_suffix}(text);
            if (navigator.clipboard && navigator.clipboard.writeText) {{
                navigator.clipboard.writeText(text).catch(function() {{}});
            }}
            try {{
                if (vipData && (vipData.name || vipData.phone || vipData.address)) {{
                    vipData.saved_at = new Date().toISOString();
                    localStorage.setItem("dayicecream_vip_member_v1", JSON.stringify(vipData));
                }}
            }} catch (e) {{}}

            var statusEl = document.getElementById("copyStatus_{button_id_suffix}");
            if (statusEl) {{
                statusEl.style.display = "block";
                if (channelName === "FB") {{
                    statusEl.innerHTML = "✅ คัดลอกบิลสั่งซื้อลงมือถือเรียบร้อยแล้ว! กำลังเปิด Facebook Page — กด 'วาง (Paste)' ส่งในแชทได้เลยครับ 👑 (บันทึกข้อมูลสมาชิก VIP เรียบร้อย)";
                }} else {{
                    statusEl.innerHTML = "✅ คัดลอกบิลสั่งซื้อ & เตรียมข้อความเข้า LINE: Dayinterfood เรียบร้อยแล้ว! กดส่งหรือกด 'วาง (Paste)' ในแชท LINE ได้ใน 1 วินาทีครับ 👑";
                }}
                syncOrderBtnHeight_{button_id_suffix}();
            }}
        }}

        function syncOrderBtnHeight_{button_id_suffix}() {{
            var root = document.getElementById("order-buttons-root-{button_id_suffix}");
            if (window.frameElement && root) {{
                window.frameElement.style.height = (root.offsetHeight + 10) + "px";
            }}
        }}
        window.addEventListener("load", syncOrderBtnHeight_{button_id_suffix});
        window.addEventListener("resize", syncOrderBtnHeight_{button_id_suffix});
        setTimeout(syncOrderBtnHeight_{button_id_suffix}, 100);
        setTimeout(syncOrderBtnHeight_{button_id_suffix}, 400);
    </script>
    """
    components.html(html_block, height=165, scrolling=False)


def render_copy_and_line_buttons(order_text: str, button_id_suffix: str) -> None:
    """ฟังก์ชันเชื่อมต่อปุ่มส่งบิลเข้า LINE และ Facebook (สำหรับหน้าจัดเลี้ยงและหน้าสั่งซื้อ)"""
    render_one_click_order_to_chat_buttons(
        order_text=order_text,
        button_id_suffix=button_id_suffix,
        fb_page_url="https://www.facebook.com/dayicecream",
        vip_payload=None,
    )


def inject_pwa_head_metadata(pwa_assets: dict[str, str]) -> None:
    """
    ฝัง Manifest (/app/static/manifest.json), Icons และ Service Worker (/app/static/sw.js)
    พร้อมดักจับ beforeinstallprompt ของเบราว์เซอร์จริงอย่างปลอดภัย (ทุกคำสั่งหุ้มด้วย try...catch)
    """
    icon_512_b64 = pwa_assets.get("icon_512_b64", "") or pwa_assets.get("logo_png_b64", "")
    icon_180_b64 = pwa_assets.get("icon_180_b64", "") or icon_512_b64
    icon_ico_b64 = pwa_assets.get("icon_ico_b64", "")

    early_boot_html = f"""
    <style>
        iframe[height="0"], iframe[height="1"] {{
            display: none !important;
            height: 0 !important;
            min-height: 0 !important;
            margin: 0 !important;
            padding: 0 !important;
            border: none !important;
        }}
        .stCustomComponentV1:has(iframe[height="0"]),
        .stElementContainer:has(iframe[height="0"]),
        .stCustomComponentV1:has(iframe[height="1"]),
        .stElementContainer:has(iframe[height="1"]),
        .stElementContainer:has(#day-pwa-early-boot) {{
            height: 0 !important;
            min-height: 0 !important;
            margin: 0 !important;
            padding: 0 !important;
            overflow: hidden !important;
        }}
    </style>
    <div id="day-pwa-early-boot" style="height:0;overflow:hidden;"></div>
    <script>
    (function() {{
        try {{
            if (!window.__dayPwaListenerAttached) {{
                window.__dayPwaListenerAttached = true;
                window.addEventListener("beforeinstallprompt", function(e) {{
                    try {{ e.preventDefault(); }} catch (err) {{}}
                    window.deferredPrompt = e;
                    window.__dayDeferredPrompt = e;
                    try {{
                        window.dispatchEvent(new CustomEvent("day-pwa-prompt-ready"));
                    }} catch (err) {{}}
                }});
                window.addEventListener("appinstalled", function() {{
                    window.deferredPrompt = null;
                    window.__dayDeferredPrompt = null;
                    window.__dayAppInstalledReal = true;
                    try {{
                        window.dispatchEvent(new CustomEvent("day-pwa-installed-real"));
                    }} catch (err) {{}}
                }});
            }}
        }} catch (e) {{}}

        try {{
            var doc = document;
            if (doc && doc.head && !doc.getElementById("day-pwa-head-v008")) {{
                var oldMarkers = doc.head.querySelectorAll("#day-pwa-head-injected, #day-pwa-head-v004, #day-pwa-head-v005, #day-pwa-head-v006, #day-pwa-head-v007, #day-pwa-head-v008, link[rel*='icon'], link[rel='apple-touch-icon'], link[rel='manifest']");
                for (var i = 0; i < oldMarkers.length; i++) {{
                    if (oldMarkers[i] && oldMarkers[i].parentNode) {{
                        oldMarkers[i].parentNode.removeChild(oldMarkers[i]);
                    }}
                }}

                var marker = doc.createElement("meta");
                marker.id = "day-pwa-head-v008";
                marker.name = "apple-mobile-web-app-title";
                marker.content = "Day Ice Cream";
                doc.head.appendChild(marker);

                var metaCap = doc.createElement("meta");
                metaCap.name = "apple-mobile-web-app-capable";
                metaCap.content = "yes";
                doc.head.appendChild(metaCap);

                var metaMob = doc.createElement("meta");
                metaMob.name = "mobile-web-app-capable";
                metaMob.content = "yes";
                doc.head.appendChild(metaMob);

                var metaAppName = doc.createElement("meta");
                metaAppName.name = "application-name";
                metaAppName.content = "Day Ice Cream";
                doc.head.appendChild(metaAppName);

                var metaTheme = doc.createElement("meta");
                metaTheme.name = "theme-color";
                metaTheme.content = "#d32f2f";
                doc.head.appendChild(metaTheme);

                var appleIcon180 = doc.createElement("link");
                appleIcon180.rel = "apple-touch-icon";
                appleIcon180.sizes = "180x180";
                appleIcon180.href = "data:image/png;base64,{icon_180_b64}";
                doc.head.appendChild(appleIcon180);

                var appleIcon512 = doc.createElement("link");
                appleIcon512.rel = "apple-touch-icon";
                appleIcon512.sizes = "512x512";
                appleIcon512.href = "data:image/png;base64,{icon_512_b64}";
                doc.head.appendChild(appleIcon512);

                var pngIcon512 = doc.createElement("link");
                pngIcon512.rel = "icon";
                pngIcon512.type = "image/png";
                pngIcon512.sizes = "512x512";
                pngIcon512.href = "/app/static/app_icon_512.png";
                doc.head.appendChild(pngIcon512);

                var pngIcon192 = doc.createElement("link");
                pngIcon192.rel = "icon";
                pngIcon192.type = "image/png";
                pngIcon192.sizes = "192x192";
                pngIcon192.href = "/app/static/app_icon_192.png";
                doc.head.appendChild(pngIcon192);

                var icoIcon = doc.createElement("link");
                icoIcon.rel = "shortcut icon";
                icoIcon.type = "image/x-icon";
                icoIcon.href = "data:image/x-icon;base64,{icon_ico_b64}";
                doc.head.appendChild(icoIcon);

                var manifestLink = doc.createElement("link");
                manifestLink.rel = "manifest";
                manifestLink.href = "/app/static/manifest.json";
                doc.head.appendChild(manifestLink);
            }}
        }} catch (e) {{}}

        try {{
            if (navigator && "serviceWorker" in navigator && !window.__daySwRegistered) {{
                window.__daySwRegistered = true;
                navigator.serviceWorker.register("/app/static/sw.js", {{ scope: "/" }}).catch(function() {{
                    navigator.serviceWorker.register("/app/static/sw.js").catch(function() {{}});
                }});
            }}
        }} catch (e) {{}}
    }})();
    </script>
    """
    st.html(early_boot_html, unsafe_allow_javascript=True)


def render_pwa_install_banner(location_key: str, pwa_assets: dict[str, str]) -> None:
    """
    ระบบติดตั้งแอป PWA ฉบับลื่นไหลสูงสุดตามโจทย์ของพี่เดย์:
    1) ลูกค้าใน TikTok / Facebook สามารถค้นหา 300+ สาขา และสั่งไอศกรีมบนหน้าเว็บได้ทันทีโดยไม่มีป๊อปอัปบังหน้าจอ
    2) เมื่อลูกค้ากดที่แบนเนอร์หรือปุ่มสีเหลืองเพื่อติดตั้งแอป:
       - หากยังอยู่ใน TikTok / Facebook: เด้งหน้าต่างกราฟิกสวยๆ ชี้มุมขวาบน บอกสั้นๆ แค่ 2 ขั้นตอน:
         "1. จิ้มจุด 3 จุด (⋯) มุมขวาบนสุด -> 2. กด 'เปิดในเบราว์เซอร์' เพื่อติดตั้งแอปลงมือถือทันทีครับ"
       - พอหน้าเว็บเปิดในเบราว์เซอร์ (Chrome / Samsung Internet) ปุ๊บ: ระบบเด้งป๊อปอัปถาม "[ติดตั้งแอป Day Ice Cream]"
         ขึ้นมาให้ลูกค้ากดยืนยันติดตั้งได้ทันทีในคลิกเดียว โดยไม่ต้องกดจุด 3 จุดซ้ำอีก!
    """
    _ = pwa_assets
    safe_key = re.sub(r"[^a-zA-Z0-9_]", "_", location_key)
    hero_banner_b64 = get_real_qr_banner_web_b64("011")

    # ภาพกราฟิกที่ 1: สำหรับผู้เข้าผ่าน TikTok / Facebook / YouTube — สั้น กระชับ ชัดเจน เพียง 2 ขั้นตอน!
    inapp_guide_svg_raw = """
    <svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 680 300" width="100%" height="auto">
      <defs>
        <linearGradient id="bgInApp" x1="0" y1="0" x2="0" y2="1">
          <stop offset="0%" stop-color="#fffbeb"/>
          <stop offset="100%" stop-color="#fef3c7"/>
        </linearGradient>
        <linearGradient id="topBarInApp" x1="0" y1="0" x2="1" y2="0">
          <stop offset="0%" stop-color="#0f172a"/>
          <stop offset="100%" stop-color="#1e293b"/>
        </linearGradient>
        <linearGradient id="stepRedInApp" x1="0" y1="0" x2="1" y2="0">
          <stop offset="0%" stop-color="#dc2626"/>
          <stop offset="100%" stop-color="#b91c1c"/>
        </linearGradient>
        <linearGradient id="stepGreenInApp" x1="0" y1="0" x2="1" y2="0">
          <stop offset="0%" stop-color="#16a34a"/>
          <stop offset="100%" stop-color="#15803d"/>
        </linearGradient>
      </defs>
      <rect x="4" y="4" width="672" height="292" rx="24" fill="url(#bgInApp)" stroke="#f59e0b" stroke-width="5"/>

      <!-- แถบจำลองหัวหน้าจอ TikTok / Facebook + ปุ่มจุด 3 จุด (⋯) มุมขวาบนสุด -->
      <rect x="24" y="18" width="632" height="62" rx="14" fill="url(#topBarInApp)"/>
      <text x="40" y="56" fill="#ffffff" font-family="Kanit, Prompt, sans-serif" font-size="21" font-weight="800">📱 มุมขวาบนสุดของจอ TikTok / Facebook</text>

      <!-- วงกลมไฮไลต์ปุ่ม ⋯ มุมขวาบนสุด -->
      <circle cx="614" cy="49" r="24" fill="#ef4444" stroke="#fde047" stroke-width="4"/>
      <circle cx="603" cy="49" r="3.5" fill="#ffffff"/>
      <circle cx="614" cy="49" r="3.5" fill="#ffffff"/>
      <circle cx="625" cy="49" r="3.5" fill="#ffffff"/>

      <!-- ขั้นที่ 1: ลูกศรชี้ไปที่ปุ่ม ⋯ มุมขวาบนสุด -->
      <rect x="190" y="94" width="464" height="64" rx="16" fill="url(#stepRedInApp)" stroke="#fde047" stroke-width="3.5"/>
      <path d="M598 94 L614 74 L630 94 Z" fill="#dc2626"/>
      <text x="422" y="134" text-anchor="middle" fill="#ffffff" font-family="Kanit, Prompt, sans-serif" font-size="22" font-weight="900">1. จิ้มจุด 3 จุด (⋯) มุมขวาบนสุด ↗</text>

      <!-- ขั้นที่ 2: กด เปิดในเบราว์เซอร์ เพื่อติดตั้งแอปลงมือถือทันทีครับ -->
      <rect x="24" y="174" width="632" height="102" rx="18" fill="#ffffff" stroke="#16a34a" stroke-width="4.5"/>
      <rect x="42" y="194" width="56" height="62" rx="14" fill="url(#stepGreenInApp)"/>
      <text x="70" y="235" text-anchor="middle" fill="#ffffff" font-family="Kanit, Prompt, sans-serif" font-size="30" font-weight="900">2</text>
      <text x="116" y="218" fill="#15803d" font-family="Kanit, Prompt, sans-serif" font-size="23" font-weight="900">2. กด “เปิดในเบราว์เซอร์ (Open in Browser)”</text>
      <text x="116" y="252" fill="#b91c1c" font-family="Kanit, Prompt, sans-serif" font-size="20" font-weight="900">👉 เพื่อติดตั้งแอปลงมือถือทันทีครับ!</text>
    </svg>
    """
    inapp_guide_svg_b64 = base64.b64encode(inapp_guide_svg_raw.strip().encode("utf-8")).decode("ascii")

    # ภาพกราฟิกที่ 2: สำหรับ iPhone Safari หรือเบราว์เซอร์ที่ยังไม่รองรับ beforeinstallprompt
    browser_guide_svg_raw = """
    <svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 680 410" width="100%" height="auto">
      <defs>
        <linearGradient id="bgBr" x1="0" y1="0" x2="0" y2="1">
          <stop offset="0%" stop-color="#fffbeb"/>
          <stop offset="100%" stop-color="#fef3c7"/>
        </linearGradient>
      </defs>
      <rect x="4" y="4" width="672" height="402" rx="24" fill="url(#bgBr)" stroke="#f59e0b" stroke-width="5"/>

      <!-- กล่องที่ 1: Google Chrome (⋮ มุมขวาบน) -->
      <rect x="24" y="20" width="632" height="114" rx="18" fill="#ffffff" stroke="#16a34a" stroke-width="4"/>
      <rect x="40" y="38" width="54" height="78" rx="12" fill="#16a34a"/>
      <text x="67" y="86" text-anchor="middle" fill="#ffffff" font-family="Kanit, Prompt, sans-serif" font-size="26" font-weight="900">⋮</text>
      <text x="110" y="56" fill="#15803d" font-family="Kanit, Prompt, sans-serif" font-size="21.5" font-weight="900">1) สำหรับ Google Chrome (Android):</text>
      <text x="110" y="86" fill="#1f2937" font-family="Kanit, Prompt, sans-serif" font-size="19.5" font-weight="800">กดปุ่มสีเขียวด้านบนเพื่อติดตั้งทันที หรือแตะ (⋮) มุมขวาบน</text>
      <text x="110" y="114" fill="#b91c1c" font-family="Kanit, Prompt, sans-serif" font-size="19.5" font-weight="900">&gt; เลือก “ติดตั้งแอป (Install app)” หรือ “เพิ่มลงในหน้าจอหลัก”</text>

      <!-- กล่องที่ 2: Samsung Internet (☰ มุมขวาล่าง) -->
      <rect x="24" y="148" width="632" height="114" rx="18" fill="#ffffff" stroke="#2563eb" stroke-width="4"/>
      <rect x="40" y="166" width="54" height="78" rx="12" fill="#2563eb"/>
      <text x="67" y="214" text-anchor="middle" fill="#ffffff" font-family="Kanit, Prompt, sans-serif" font-size="26" font-weight="900">☰</text>
      <text x="110" y="184" fill="#1d4ed8" font-family="Kanit, Prompt, sans-serif" font-size="21.5" font-weight="900">2) สำหรับมือถือ Samsung (Samsung Internet):</text>
      <text x="110" y="214" fill="#1f2937" font-family="Kanit, Prompt, sans-serif" font-size="19.5" font-weight="800">กดปุ่มสีเขียวด้านบนเพื่อติดตั้งทันที หรือแตะ (☰) มุมขวาล่าง</text>
      <text x="110" y="242" fill="#b91c1c" font-family="Kanit, Prompt, sans-serif" font-size="19.5" font-weight="900">&gt; กด “+ เพิ่มหน้าไปยัง (Add page to)” &gt; เลือก “หน้าจอหลัก”</text>

      <!-- กล่องที่ 3: iPhone / iPad Safari (ปุ่มแชร์ ⬆️ ด้านล่าง) -->
      <rect x="24" y="276" width="632" height="112" rx="18" fill="#ffffff" stroke="#d97706" stroke-width="4"/>
      <rect x="40" y="294" width="54" height="76" rx="12" fill="#d97706"/>
      <text x="67" y="341" text-anchor="middle" fill="#ffffff" font-family="Kanit, Prompt, sans-serif" font-size="24" font-weight="900">⬆️</text>
      <text x="110" y="312" fill="#b45309" font-family="Kanit, Prompt, sans-serif" font-size="21.5" font-weight="900">3) สำหรับ iPhone / iPad (Safari):</text>
      <text x="110" y="342" fill="#1f2937" font-family="Kanit, Prompt, sans-serif" font-size="19.5" font-weight="800">แตะปุ่มแชร์ (Share ⬆️) แถบด้านล่างของจอ</text>
      <text x="110" y="369" fill="#b91c1c" font-family="Kanit, Prompt, sans-serif" font-size="19.5" font-weight="900">&gt; เลื่อนลงมาเลือก “เพิ่มไปยังหน้าจอโฮม (Add to Home Screen)”</text>
    </svg>
    """
    browser_guide_svg_b64 = base64.b64encode(browser_guide_svg_raw.strip().encode("utf-8")).decode("ascii")

    banner_html = f"""
    <style>
        .day-pwa-toggle-chk {{
            display: none !important;
        }}
        .day-pizza-banner-wrap {{
            display: block !important;
            width: 100% !important;
            height: auto !important;
            margin-top: 8px !important;
            margin-bottom: 18px !important;
            position: relative !important;
            clear: both !important;
            z-index: 20 !important;
            font-family: 'Kanit', 'Prompt', sans-serif !important;
        }}
        .day-pwa-direct-card {{
            width: 100% !important;
            height: auto !important;
            display: flex !important;
            flex-direction: column !important;
            background: linear-gradient(135deg, #7f1017 0%, #b91c1c 48%, #991b1b 100%) !important;
            color: #ffffff !important;
            border: 3.5px solid #FFD700 !important;
            border-radius: 22px !important;
            padding: 0 !important;
            cursor: pointer !important;
            text-align: left !important;
            box-shadow: 0 12px 30px rgba(185, 28, 28, 0.34) !important;
            transition: transform 0.14s ease, box-shadow 0.14s ease !important;
            box-sizing: border-box !important;
            position: relative !important;
            overflow: hidden !important;
            text-decoration: none !important;
            margin: 0 !important;
            user-select: none !important;
            -webkit-tap-highlight-color: transparent !important;
        }}
        .day-pwa-direct-card:hover {{
            transform: translateY(-1px) !important;
            box-shadow: 0 14px 34px rgba(185, 28, 28, 0.45), 0 0 20px rgba(255, 215, 0, 0.5) !important;
        }}
        .day-pwa-direct-card:active {{
            transform: scale(0.99) !important;
        }}
        .day-pizza-close-x {{
            position: absolute !important;
            top: 12px !important;
            right: 12px !important;
            width: 34px !important;
            height: 34px !important;
            border-radius: 50% !important;
            background: rgba(0, 0, 0, 0.68) !important;
            color: #ffffff !important;
            border: 2px solid #fde047 !important;
            display: flex !important;
            align-items: center !important;
            justify-content: center !important;
            font-size: 16px !important;
            font-weight: 900 !important;
            line-height: 1 !important;
            cursor: pointer !important;
            z-index: 30 !important;
            transition: all 0.15s ease !important;
            box-shadow: 0 3px 10px rgba(0,0,0,0.45) !important;
        }}
        .day-4k-img-container {{
            width: 100% !important;
            position: relative !important;
            display: block !important;
            line-height: 0 !important;
            background: #450a0a !important;
            cursor: pointer !important;
            pointer-events: none !important;
        }}
        .day-4k-realqr-hero-img {{
            width: 100% !important;
            height: auto !important;
            display: block !important;
            object-fit: contain !important;
            cursor: pointer !important;
            pointer-events: none !important;
        }}
        .day-4k-bottom-cta-strip {{
            width: 100% !important;
            background: linear-gradient(90deg, #65090e 0%, #991b1b 50%, #65090e 100%) !important;
            border-top: 2.5px solid #fde047 !important;
            padding: 10px 16px !important;
            display: flex !important;
            align-items: center !important;
            justify-content: center !important;
            box-sizing: border-box !important;
            cursor: pointer !important;
            pointer-events: none !important;
        }}
        .day-pizza-install-btn {{
            display: inline-flex !important;
            align-items: center !important;
            justify-content: center !important;
            gap: 8px !important;
            width: 100% !important;
            background: linear-gradient(135deg, #fef08a 0%, #facc15 100%) !important;
            color: #7f1d1d !important;
            font-size: 15.5px !important;
            font-weight: 900 !important;
            padding: 10px 20px !important;
            border-radius: 999px !important;
            border: 2px solid #ffffff !important;
            box-shadow: 0 4px 14px rgba(0, 0, 0, 0.28) !important;
            cursor: pointer !important;
            text-align: center !important;
            text-decoration: none !important;
            box-sizing: border-box !important;
            pointer-events: none !important;
        }}
        /* หน้าต่าง Modal เต็มจอ + เปิดได้ทันทีทั้งด้วย CSS :checked และ JavaScript โดยไม่รีเฟรชหน้าเว็บ 100% */
        .day-pwa-guide-overlay {{
            display: none;
            position: fixed !important;
            inset: 0 !important;
            background: rgba(0, 0, 0, 0.86) !important;
            z-index: 2147483646 !important;
            align-items: center !important;
            justify-content: center !important;
            padding: 14px !important;
            box-sizing: border-box !important;
            backdrop-filter: blur(6px) !important;
            font-family: 'Kanit', 'Prompt', sans-serif !important;
            overflow-y: auto !important;
        }}
        #day-pwa-toggle-{safe_key}:checked ~ .day-pwa-guide-overlay {{
            display: flex !important;
        }}
        .day-pwa-topright-pointer {{
            position: fixed !important;
            top: 10px !important;
            right: 12px !important;
            background: linear-gradient(135deg, #fef08a 0%, #facc15 100%) !important;
            color: #7f1d1d !important;
            border: 3px solid #dc2626 !important;
            border-radius: 16px !important;
            padding: 8px 14px !important;
            font-size: 15px !important;
            font-weight: 900 !important;
            box-shadow: 0 8px 24px rgba(0,0,0,0.75) !important;
            z-index: 2147483647 !important;
            animation: dayBounceArrow 0.9s infinite alternate !important;
        }}
        @keyframes dayBounceArrow {{
            0% {{ transform: translateY(0px); }}
            100% {{ transform: translateY(7px); }}
        }}
        .day-pwa-guide-card {{
            background: linear-gradient(160deg, #7f1017 0%, #b91c1c 55%, #991b1b 100%) !important;
            color: #ffffff !important;
            border: 3.5px solid #FFD700 !important;
            border-radius: 24px !important;
            padding: 20px 16px !important;
            max-width: 460px !important;
            width: 100% !important;
            box-shadow: 0 24px 60px rgba(0,0,0,0.88) !important;
            text-align: center !important;
            position: relative !important;
            box-sizing: border-box !important;
            margin-top: 36px !important;
        }}
        .day-pwa-guide-img {{
            width: 100% !important;
            height: auto !important;
            border-radius: 16px !important;
            display: block !important;
            margin: 0 auto 12px auto !important;
            box-shadow: 0 8px 20px rgba(0,0,0,0.35) !important;
        }}
        .day-pwa-step-box {{
            background: rgba(0, 0, 0, 0.42) !important;
            border: 2.5px solid #fde047 !important;
            border-radius: 18px !important;
            padding: 14px 16px !important;
            margin-bottom: 12px !important;
            font-size: 16px !important;
            line-height: 1.65 !important;
            text-align: left !important;
            color: #ffffff !important;
        }}
        .day-pwa-copy-link-btn {{
            display: block !important;
            width: 100% !important;
            text-align: center !important;
            background: linear-gradient(135deg, #fef08a 0%, #facc15 100%) !important;
            color: #7f1d1d !important;
            font-weight: 900 !important;
            font-size: 15.5px !important;
            padding: 13px 14px !important;
            border-radius: 999px !important;
            border: 2.5px solid #ffffff !important;
            box-shadow: 0 6px 18px rgba(0,0,0,0.38) !important;
            margin-bottom: 10px !important;
            box-sizing: border-box !important;
            cursor: pointer !important;
            font-family: 'Kanit', 'Prompt', sans-serif !important;
        }}
        .day-pwa-copy-link-btn:active {{
            transform: scale(0.98) !important;
        }}
        .day-pwa-native-prompt-btn {{
            display: none;
            width: 100% !important;
            text-align: center !important;
            background: linear-gradient(135deg, #22c55e 0%, #16a34a 100%) !important;
            color: #ffffff !important;
            font-weight: 900 !important;
            font-size: 18px !important;
            padding: 16px 18px !important;
            border-radius: 999px !important;
            border: 3px solid #fef08a !important;
            box-shadow: 0 10px 26px rgba(22, 163, 74, 0.6) !important;
            margin-bottom: 12px !important;
            box-sizing: border-box !important;
            cursor: pointer !important;
            font-family: 'Kanit', 'Prompt', sans-serif !important;
            text-decoration: none !important;
        }}
        .day-pwa-guide-close-btn {{
            display: block !important;
            width: 100% !important;
            text-align: center !important;
            background: rgba(255,255,255,0.20) !important;
            color: #fef08a !important;
            font-weight: 800 !important;
            font-size: 14.5px !important;
            padding: 11px 14px !important;
            border-radius: 999px !important;
            border: 1.5px solid #fde047 !important;
            cursor: pointer !important;
            margin-top: 6px !important;
            box-sizing: border-box !important;
            font-family: 'Kanit', 'Prompt', sans-serif !important;
        }}
        @media (max-width: 768px) {{
            .day-pizza-banner-wrap {{ margin-top: 6px !important; margin-bottom: 18px !important; height: auto !important; }}
            .day-4k-bottom-cta-strip {{ padding: 8px 10px !important; }}
            .day-pizza-install-btn {{ font-size: 12.5px !important; padding: 8px 12px !important; width: 100% !important; }}
        }}
    </style>

    <input type="checkbox" id="day-pwa-toggle-{safe_key}" class="day-pwa-toggle-chk" />

    <div class="day-pizza-banner-wrap" id="day-pizza-wrap-{safe_key}">
        <button type="button" class="day-pizza-close-x" id="day-pwa-hide-btn-{safe_key}" title="ปิดแถบแบนเนอร์นี้">✕</button>
        <!-- คลิกได้ทั้งกรอบใหญ่ทั้งหมด: ทั้งรูปภาพแบนเนอร์สีแดงอันใหญ่ และปุ่มแถบสีเหลืองด้านล่าง -->
        <label for="day-pwa-toggle-{safe_key}" class="day-pwa-direct-card" id="day-pwa-card-{safe_key}">
            <div class="day-4k-img-container">
                <img class="day-4k-realqr-hero-img" src="data:image/jpeg;base64,{hero_banner_b64}" alt="โหลด App Day Ice Cream" />
            </div>
            <div class="day-4k-bottom-cta-strip">
                <span class="day-pizza-install-btn" id="day-pwa-btn-{safe_key}">📲 กดปุ่มนี้เพื่อติดตั้งแอป Day Ice Cream ลงมือถือของคุณลูกค้า (คลิกที่นี่ ❯)</span>
            </div>
        </label>
    </div>

    <!-- หน้าต่าง Modal เต็มจอ (ไม่มีการรีเฟรชหน้าเว็บ 100%) -->
    <div class="day-pwa-guide-overlay" id="day-pwa-modal-{safe_key}">
        <div class="day-pwa-topright-pointer" id="day-pwa-pointer-{safe_key}">
            ↗ 1. จิ้มจุด 3 จุด (⋯) มุมขวาบนสุดของหน้าจอนี้!
        </div>
        <div class="day-pwa-guide-card" id="day-pwa-modal-card-{safe_key}">
            <img id="day-pwa-confirm-icon-{safe_key}" src="/app/static/app_icon_192.png" alt="Day Ice Cream" style="display:none;width:82px;height:82px;border-radius:20px;margin:0 auto 10px auto;border:3px solid #fde047;box-shadow:0 6px 18px rgba(0,0,0,0.45);" />
            <div id="day-pwa-modal-title-{safe_key}" style="font-size:19px;font-weight:900;color:#fef08a;margin-bottom:10px;line-height:1.35;">
                📲 วิธีติดตั้งแอปลงมือถือ (เพียง 2 ขั้นตอนง่ายๆ):
            </div>
            <button type="button" class="day-pwa-native-prompt-btn" id="day-pwa-native-btn-{safe_key}">
                📲 [ติดตั้งแอป Day Ice Cream] กดยืนยันที่นี่ ❯
            </button>
            <div class="day-pwa-step-box" id="day-pwa-tiktok-box-{safe_key}">
                <div style="font-weight:900;color:#fde047;font-size:17px;margin-bottom:6px;">👉 ทำตาม 2 ขั้นตอนสั้นๆ นี้ได้เลยครับ:</div>
                <b>1.</b> จิ้มจุด 3 จุด <b>(⋯)</b> มุมขวาบนสุด ↗<br/>
                <b>2.</b> กด <b>&ldquo;เปิดในเบราว์เซอร์ (Open in Browser)&rdquo;</b> เพื่อติดตั้งแอปลงมือถือทันทีครับ!
            </div>
            <img class="day-pwa-guide-img" id="day-pwa-guide-img-{safe_key}" src="data:image/svg+xml;base64,{inapp_guide_svg_b64}" alt="ขั้นตอนการติดตั้งแอป Day Ice Cream ลงมือถือ" />
            <button type="button" id="day-pwa-copy-btn-{safe_key}" class="day-pwa-copy-link-btn">
                📋 หรือกดคัดลอกลิงก์ไปเปิดใน Chrome / Safari
            </button>
            <div class="day-pwa-step-box" id="day-pwa-modal-desc-{safe_key}" style="display:none;margin-bottom:8px;font-size:14px;">
                <b style="color:#fde047;">🌐 สำหรับ iPhone (Safari) หรือเบราว์เซอร์ทั่วไป:</b><br/>
                • <b>iPhone / iPad (Safari):</b> แตะปุ่มแชร์ <b>(⬆️) ด้านล่าง</b> &gt; เลือก <b>&ldquo;เพิ่มไปยังหน้าจอโฮม (Add to Home Screen)&rdquo;</b><br/>
                • <b>Chrome / Samsung Internet:</b> แตะเมนู <b>(⋮)</b> หรือ <b>(☰)</b> &gt; เลือก <b>&ldquo;ติดตั้งแอป / เพิ่มลงในหน้าจอหลัก&rdquo;</b>
            </div>
            <label for="day-pwa-toggle-{safe_key}" class="day-pwa-guide-close-btn" id="day-pwa-close-modal-{safe_key}">✕ ปิดหน้าต่างนี้ (ค้นหาสาขา / สั่งไอศกรีมบนหน้าเว็บต่อ)</label>
        </div>
    </div>

    <script>
        (function() {{
            var appUrlToCopy = "https://app.dayicecream.com";
            var inappSvgSrc = "data:image/svg+xml;base64,{inapp_guide_svg_b64}";
            var browserSvgSrc = "data:image/svg+xml;base64,{browser_guide_svg_b64}";

            var chkEl = document.getElementById("day-pwa-toggle-{safe_key}");
            var wrapEl = document.getElementById("day-pizza-wrap-{safe_key}");
            var cardEl = document.getElementById("day-pwa-card-{safe_key}");
            var btnEl = document.getElementById("day-pwa-btn-{safe_key}");
            var hideBtnEl = document.getElementById("day-pwa-hide-btn-{safe_key}");

            var modalEl = document.getElementById("day-pwa-modal-{safe_key}");
            var pointerEl = document.getElementById("day-pwa-pointer-{safe_key}");
            var modalCardEl = document.getElementById("day-pwa-modal-card-{safe_key}");
            var confirmIconEl = document.getElementById("day-pwa-confirm-icon-{safe_key}");
            var modalTitleEl = document.getElementById("day-pwa-modal-title-{safe_key}");
            var tiktokBoxEl = document.getElementById("day-pwa-tiktok-box-{safe_key}");
            var nativeBtnEl = document.getElementById("day-pwa-native-btn-{safe_key}");
            var guideImgEl = document.getElementById("day-pwa-guide-img-{safe_key}");
            var copyBtnEl = document.getElementById("day-pwa-copy-btn-{safe_key}");
            var descBoxEl = document.getElementById("day-pwa-modal-desc-{safe_key}");
            var closeModalBtnEl = document.getElementById("day-pwa-close-modal-{safe_key}");

            function detectBrowserEnv() {{
                var ua = "";
                try {{
                    ua = navigator.userAgent || "";
                }} catch (e) {{}}
                var isAndroid = (new RegExp("Android", "i")).test(ua);
                var isIOS = (new RegExp("iPhone|iPad|iPod", "i")).test(ua);
                var isTikTok = (new RegExp("TikTok|musical_ly|BytedanceWebview|Bytedance|ByteLocale|Trill|aweme", "i")).test(ua);
                var isSamsung = (new RegExp("SamsungBrowser", "i")).test(ua);
                var isFacebookOrLine = (new RegExp("FBAN|FBAV|FB_IAB|FBIOS|Line/|LIFF|Messenger|Orca-Android|Instagram", "i")).test(ua);
                var isKnownInApp = isTikTok || isFacebookOrLine || (new RegExp("MicroMessenger|Twitter|wv\\\\)", "i")).test(ua);
                var isWebViewIOS = isIOS && !(new RegExp("Safari/", "i")).test(ua);
                return {{
                    ua: ua,
                    isAndroid: isAndroid,
                    isIOS: isIOS,
                    isTikTok: isTikTok,
                    isSamsung: isSamsung,
                    isFacebookOrLine: isFacebookOrLine,
                    isInAppBrowser: isKnownInApp || isWebViewIOS
                }};
            }}

            function getDeferredPrompt() {{
                var dp = window.deferredPrompt || window.__dayDeferredPrompt || null;
                if (!dp) {{
                    try {{
                        if (window.top) {{
                            dp = window.top.deferredPrompt || window.top.__dayDeferredPrompt || null;
                        }}
                    }} catch (e) {{}}
                }}
                if (!dp) {{
                    try {{
                        if (window.parent) {{
                            dp = window.parent.deferredPrompt || window.parent.__dayDeferredPrompt || null;
                        }}
                    }} catch (e) {{}}
                }}
                return dp;
            }}

            function triggerRealBrowserInstallPrompt() {{
                var dp = getDeferredPrompt();
                if (dp && typeof dp.prompt === "function") {{
                    try {{
                        dp.prompt();
                        if (dp.userChoice && typeof dp.userChoice.then === "function") {{
                            dp.userChoice.then(function(choiceResult) {{
                                if (choiceResult && choiceResult.outcome === "accepted") {{
                                    window.deferredPrompt = null;
                                    window.__dayDeferredPrompt = null;
                                    try {{
                                        if (window.top) {{
                                            window.top.deferredPrompt = null;
                                            window.top.__dayDeferredPrompt = null;
                                        }}
                                    }} catch (e) {{}}
                                    if (btnEl) {{
                                        btnEl.innerHTML = "✅ ติดตั้งแอป Day Ice Cream ลงเครื่องเรียบร้อยแล้ว";
                                    }}
                                    if (chkEl) {{
                                        chkEl.checked = false;
                                    }}
                                    if (modalEl) {{
                                        modalEl.style.display = "none";
                                    }}
                                }}
                            }});
                        }}
                        return true;
                    }} catch (err) {{}}
                }}
                return false;
            }}

            function configureModalContent() {{
                var env = detectBrowserEnv();
                var dp = getDeferredPrompt();
                var hasNativePrompt = Boolean(dp && typeof dp.prompt === "function");

                if (env.isInAppBrowser) {{
                    // กรณีอยู่ใน TikTok / Facebook: แสดงเฉพาะกราฟิก 2 ขั้นตอนสั้นๆ ชี้ไปที่มุมขวาบน
                    if (confirmIconEl) confirmIconEl.style.display = "none";
                    if (modalTitleEl) {{
                        modalTitleEl.innerHTML = "📲 ติดตั้งแอปลงมือถือ (เพียง 2 ขั้นตอนง่ายๆ):";
                    }}
                    if (pointerEl) {{
                        pointerEl.style.display = "block";
                        pointerEl.innerHTML = "↗ 1. จิ้มจุด 3 จุด (⋯) มุมขวาบนสุดของหน้าจอนี้!";
                    }}
                    if (nativeBtnEl) nativeBtnEl.style.display = "none";
                    if (tiktokBoxEl) tiktokBoxEl.style.display = "block";
                    if (guideImgEl) {{
                        guideImgEl.style.display = "block";
                        guideImgEl.src = inappSvgSrc;
                    }}
                    if (copyBtnEl) copyBtnEl.style.display = "block";
                    if (descBoxEl) descBoxEl.style.display = "none";
                }} else if (hasNativePrompt) {{
                    // กรณีเปิดในเบราว์เซอร์ (Chrome / Samsung Internet) และพร้อมติดตั้งทันที:
                    // เด้งป๊อปอัปถาม "[ติดตั้งแอป Day Ice Cream]" ให้กดยืนยันได้ทันทีโดยไม่ต้องกดจุด 3 จุด!
                    if (confirmIconEl) confirmIconEl.style.display = "block";
                    if (modalTitleEl) {{
                        modalTitleEl.innerHTML = "🍦 ต้องการติดตั้งแอป Day Ice Cream ลงหน้าจอมือถือไหมครับ?";
                    }}
                    if (pointerEl) pointerEl.style.display = "none";
                    if (nativeBtnEl) nativeBtnEl.style.display = "block";
                    if (tiktokBoxEl) tiktokBoxEl.style.display = "none";
                    if (guideImgEl) guideImgEl.style.display = "none";
                    if (copyBtnEl) copyBtnEl.style.display = "none";
                    if (descBoxEl) descBoxEl.style.display = "none";
                }} else {{
                    // กรณี iPhone (Safari) หรือเบราว์เซอร์ทั่วไปที่กดปุ่มติดตั้ง
                    if (confirmIconEl) confirmIconEl.style.display = "none";
                    if (modalTitleEl) {{
                        modalTitleEl.innerHTML = "📲 วิธีติดตั้งแอป Day Ice Cream ลงหน้าจอมือถือ";
                    }}
                    if (pointerEl) {{
                        pointerEl.style.display = "block";
                        pointerEl.innerHTML = env.isSamsung
                            ? "↘ แตะปุ่มขีด 3 ขีด (☰) มุมขวาล่าง เพื่อเพิ่มลงหน้าจอหลัก!"
                            : (env.isIOS
                                ? "⬇️ แตะปุ่มแชร์ (⬆️) ด้านล่าง > เลือก เพิ่มไปยังหน้าจอโฮม!"
                                : "↗ แตะปุ่มจุด 3 จุด (⋮) มุมขวาบนสุดของจอ!");
                    }}
                    if (nativeBtnEl) nativeBtnEl.style.display = "none";
                    if (tiktokBoxEl) tiktokBoxEl.style.display = "none";
                    if (guideImgEl) {{
                        guideImgEl.style.display = "block";
                        guideImgEl.src = browserSvgSrc;
                    }}
                    if (copyBtnEl) copyBtnEl.style.display = "none";
                    if (descBoxEl) descBoxEl.style.display = "block";
                }}
            }}

            function openModalNow() {{
                configureModalContent();
                if (chkEl) {{
                    chkEl.checked = true;
                }}
                if (modalEl) {{
                    modalEl.style.display = "flex";
                }}
            }}

            function closeModalNow() {{
                if (chkEl) {{
                    chkEl.checked = false;
                }}
                if (modalEl) {{
                    modalEl.style.display = "none";
                }}
            }}

            function onPromptBecameReady() {{
                var env = detectBrowserEnv();
                // ทันทีที่ลูกค้ากด "เปิดในเบราว์เซอร์" จาก TikTok/Facebook เข้ามาใน Chrome / Samsung Internet บนมือถือ
                // ให้เด้งป๊อปอัปถาม "[ติดตั้งแอป Day Ice Cream]" ขึ้นมาอัตโนมัติทันทีโดยไม่ต้องกดจุด 3 จุดซ้ำอีก!
                if ("{safe_key}" === "header_top" && env.isAndroid && !env.isInAppBrowser && !window.__dayAutoBrowserPromptShown) {{
                    window.__dayAutoBrowserPromptShown = true;
                    if (!triggerRealBrowserInstallPrompt()) {{
                        openModalNow();
                    }}
                }} else if (modalEl && modalEl.style.display === "flex") {{
                    configureModalContent();
                }}
            }}

            function captureBeforeInstallPrompt(e) {{
                try {{ e.preventDefault(); }} catch (err) {{}}
                window.deferredPrompt = e;
                window.__dayDeferredPrompt = e;
                try {{
                    if (window.top) {{
                        window.top.deferredPrompt = e;
                        window.top.__dayDeferredPrompt = e;
                    }}
                }} catch (err) {{}}
                onPromptBecameReady();
            }}

            try {{
                if (!window.__dayPwaBannerPromptListener) {{
                    window.__dayPwaBannerPromptListener = true;
                    window.addEventListener("beforeinstallprompt", captureBeforeInstallPrompt);
                }}
                window.addEventListener("day-pwa-prompt-ready", function() {{
                    onPromptBecameReady();
                }});
                window.addEventListener("day-pwa-installed-real", function() {{
                    if (btnEl) {{
                        btnEl.innerHTML = "✅ ติดตั้งแอป Day Ice Cream ลงเครื่องเรียบร้อยแล้ว";
                    }}
                    closeModalNow();
                }});
                // หาก beforeinstallprompt ยิงไปก่อนหน้านี้แล้ว
                if (getDeferredPrompt()) {{
                    setTimeout(onPromptBecameReady, 250);
                }}
            }} catch (e) {{}}

            // ปุ่มคัดลอกลิงก์ไปเปิดใน Chrome / Safari (ทำงานได้ในทุก WebView โดยไม่รีเฟรชหน้าเว็บ)
            if (copyBtnEl) {{
                copyBtnEl.addEventListener("click", function(ev) {{
                    ev.preventDefault();
                    ev.stopPropagation();
                    try {{
                        var ta = document.createElement("textarea");
                        ta.value = appUrlToCopy;
                        ta.setAttribute("readonly", "");
                        ta.style.position = "fixed";
                        ta.style.left = "-9999px";
                        document.body.appendChild(ta);
                        ta.focus();
                        ta.select();
                        document.execCommand("copy");
                        document.body.removeChild(ta);
                    }} catch (e) {{}}
                    try {{
                        if (navigator.clipboard && navigator.clipboard.writeText) {{
                            navigator.clipboard.writeText(appUrlToCopy).catch(function() {{}});
                        }}
                    }} catch (e) {{}}
                    copyBtnEl.innerHTML = "✅ คัดลอกลิงก์ https://app.dayicecream.com แล้ว! นำไปวางใน Chrome / Safari ได้เลยครับ";
                    copyBtnEl.style.background = "linear-gradient(135deg, #bbf7d0 0%, #4ade80 100%)";
                    copyBtnEl.style.color = "#064e3b";
                    setTimeout(function() {{
                        if (copyBtnEl) {{
                            copyBtnEl.innerHTML = "📋 หรือกดคัดลอกลิงก์ไปเปิดใน Chrome / Safari (คัดลอกสำเร็จ ✅)";
                        }}
                    }}, 3500);
                }});
            }}

            if (nativeBtnEl) {{
                nativeBtnEl.addEventListener("click", function(ev) {{
                    ev.preventDefault();
                    ev.stopPropagation();
                    triggerRealBrowserInstallPrompt();
                }});
            }}

            if (hideBtnEl && wrapEl) {{
                hideBtnEl.addEventListener("click", function(ev) {{
                    ev.preventDefault();
                    ev.stopPropagation();
                    wrapEl.style.display = "none";
                }});
            }}

            if (closeModalBtnEl) {{
                closeModalBtnEl.addEventListener("click", function(ev) {{
                    ev.preventDefault();
                    ev.stopPropagation();
                    closeModalNow();
                }});
            }}

            if (modalEl) {{
                modalEl.addEventListener("click", function(ev) {{
                    if (ev.target === modalEl) {{
                        ev.preventDefault();
                        ev.stopPropagation();
                        closeModalNow();
                    }}
                }});
            }}

            if (modalCardEl) {{
                modalCardEl.addEventListener("click", function(ev) {{
                    ev.stopPropagation();
                }});
            }}

            // คลิกที่ส่วนใดของแบนเนอร์ใหญ่ (ทั้งรูปสีแดงอันใหญ่ หรือปุ่มสีเหลืองด้านล่าง) ก็ทำงานทันที!
            if (cardEl) {{
                cardEl.addEventListener("click", function(ev) {{
                    // 1) หากเปิดในเบราว์เซอร์ (Chrome / Samsung Internet) และมี beforeinstallprompt พร้อมอยู่แล้ว
                    //    ให้เด้งหน้าต่าง [ติดตั้งแอป Day Ice Cream] ของระบบขึ้นมาทันทีใน 1 คลิก โดยไม่ต้องกดจุด 3 จุด!
                    if (triggerRealBrowserInstallPrompt()) {{
                        ev.preventDefault();
                        ev.stopPropagation();
                        closeModalNow();
                        return;
                    }}

                    // 2) หากเปิดใน TikTok / Facebook หรือยังไม่มี beforeinstallprompt
                    //    ให้เปิดหน้าต่าง Modal กราฟิก 2 ขั้นตอนกลางหน้าจอทันทีในหน้าเดิม (ไม่มีการรีเฟรชหน้าเว็บ 100%)
                    ev.preventDefault();
                    ev.stopPropagation();
                    openModalNow();
                }});
            }}
        }})();
    </script>
    """
    st.html(banner_html, unsafe_allow_javascript=True)



# ==============================================================================
# INITIALIZE ASSETS, DATA & SESSION STATE
# ==============================================================================
ensure_vip_csv_files()
CUSTOM_PIN_DATA_URI, CUSTOM_PIN_INTERNAL_DATA_URI = ensure_custom_pin_icons(force=False)
flavors_cfg = scan_and_load_flavors_config(force_rescan=False)
promo_gallery_cfg = ensure_and_load_promo_gallery(force_reset=False)
viral_videos_cfg = load_viral_videos_config()
links_cfg = sync_linktree_links(force=False)
channels_cfg = load_channels_config()
all_branches, branches_sync_status = load_branches_live()

HEADER_MAIN_LOGO_B64 = load_b64_image(str(ASSETS_DIR / "header_logo_dayicecream.jpg"))
QUALITY_BANNER_B64 = load_b64_image(str(ASSETS_DIR / "quality_banner_2565.jpg"))
LOGO_GOLD_COIN_B64 = load_b64_image(str(ASSETS_DIR / "day_gold_coin.png"))
LOGO_DAY_STORY_B64 = load_b64_image(str(ASSETS_DIR / "day_story.png"))
LOGO_DAY_SCIENCE_B64 = load_b64_image(str(ASSETS_DIR / "day_science.png"))
LOGO_DAY_THEATER_B64 = load_b64_image(str(ASSETS_DIR / "day_home_theater.png"))

PAGE_ICON_PATH = (
    (APP_DIR / "app_icon_512.png")
    if (APP_DIR / "app_icon_512.png").exists()
    else (
        (APP_DIR / "day_icecream_logo.png")
        if (APP_DIR / "day_icecream_logo.png").exists()
        else (
            (APP_DIR / "day_icecream_icon.ico")
            if (APP_DIR / "day_icecream_icon.ico").exists()
            else CUSTOM_PIN_PATH
        )
    )
)

# ตั้งค่า initial_sidebar_state="collapsed" เพื่อให้ลูกค้าเปิดเว็บมาเจอหน้าเต็มจอแบบมืออาชีพทันที
st.set_page_config(
    page_title="Day Ice Cream (เดย์ ไอศกรีม) — สั่งไอศกรีมโฮมเมด & ค้นหา 300+ สาขาทั่วไทย",
    page_icon=str(PAGE_ICON_PATH) if PAGE_ICON_PATH.exists() else "🍦",
    layout="wide",
    initial_sidebar_state="collapsed",
)

if "active_4k_banner_num" not in st.session_state:
    st.session_state["active_4k_banner_num"] = "011"

PWA_ASSETS = ensure_pwa_app_icons()
inject_pwa_head_metadata(PWA_ASSETS)

if "gps_active" not in st.session_state:
    st.session_state["gps_active"] = False
if "user_lat" not in st.session_state:
    st.session_state["user_lat"] = DEFAULT_HQ_LAT
if "user_lon" not in st.session_state:
    st.session_state["user_lon"] = DEFAULT_HQ_LON
if "user_loc_label" not in st.session_state:
    st.session_state["user_loc_label"] = "สำนักงานใหญ่ เดย์ไอศครีม (จ.นครปฐม)"

for flv in flavors_cfg.get("flavors", []):
    fid = flv["id"]
    if f"qty_flv_{fid}" not in st.session_state:
        st.session_state[f"qty_flv_{fid}"] = 0
    if flv.get("out_of_stock") and st.session_state.get(f"qty_flv_{fid}", 0) > 0:
        st.session_state[f"qty_flv_{fid}"] = 0


# ==============================================================================
# COLLAPSED BACKEND SIDEBAR (FOR P'DAY ONLY — HIDDEN BY DEFAULT FOR CUSTOMERS)
# ==============================================================================
with st.sidebar:
    sidebar_logo_html = (
        f'<img src="{CUSTOM_PIN_DATA_URI}" '
        f'style="width:52px;height:52px;border-radius:50%;background:#fff;padding:2px;box-shadow:0 4px 10px rgba(211,47,47,0.2);" />'
        if CUSTOM_PIN_DATA_URI
        else "🍦"
    )
    render_html(
        f"""
<div style="display:flex;align-items:center;gap:10px;padding:12px 14px;background:linear-gradient(135deg,#d32f2f,#ff5252);border-radius:16px;color:#fff;margin-bottom:14px;box-shadow:0 6px 18px rgba(211,47,47,0.2);">
{sidebar_logo_html}
<div>
<div style="font-weight:800;font-size:15px;line-height:1.2;">ตั้งค่าหลังบ้าน (พี่เดย์)</div>
<div style="font-size:11.5px;opacity:0.92;">จัดการวิดีโอ • สต็อก • แกลเลอรี • แผนที่</div>
</div>
</div>
"""
    )

    # 0. ระบบเปิดดูแอปบนมือถือ (Mobile Live Preview & QR Code - บนสุดของ Sidebar)
    local_lan_url = get_local_lan_url(8502)
    render_html(
        f"""
<div style="background:linear-gradient(135deg,#fff1f2,#ffe4e6);border:2px solid #d32f2f;border-radius:16px;padding:12px 14px;margin-bottom:10px;box-shadow:0 6px 16px rgba(211,47,47,0.12);">
<div style="font-size:14px;font-weight:800;color:#b71c1c;line-height:1.4;">📱 สแกน QR Code นี้ด้วยกล้องมือถือ (Wi-Fi เดียวกัน) เพื่อดูหน้าแอปบนมือถือทันที!</div>
<div style="font-size:12px;font-weight:700;color:#991b1b;margin-top:4px;background:#ffffff;padding:5px 8px;border-radius:8px;border:1px dashed #fca5a5;word-break:break-all;">🔗 {local_lan_url}</div>
</div>
"""
    )
    lan_qr_bytes = generate_qr_code_bytes(local_lan_url)
    if lan_qr_bytes:
        st.image(
            lan_qr_bytes,
            caption=f"📶 สแกนผ่าน Wi-Fi เดียวกัน ({local_lan_url})",
            use_container_width=True,
        )

    if "public_mobile_url" not in st.session_state:
        st.session_state["public_mobile_url"] = get_existing_online_tunnel_url()

    if st.button(
        "🌐 สร้างลิงก์ออนไลน์เปิดดูบนมือถือ (Cloudflare Quick Tunnel / pyngrok)",
        use_container_width=True,
        type="primary",
        key="btn_create_mobile_tunnel",
    ):
        with st.spinner("กำลังสร้างลิงก์ออนไลน์ Public URL (HTTPS) สำหรับเปิดผ่าน 4G/5G หรือส่งเข้า LINE..."):
            pub_url, pub_msg = start_online_mobile_tunnel(8502)
            if pub_url:
                st.session_state["public_mobile_url"] = pub_url
                st.success(pub_msg)
            else:
                st.warning(pub_msg)

    active_public_url = st.session_state.get("public_mobile_url", "") or get_existing_online_tunnel_url()
    if active_public_url:
        st.session_state["public_mobile_url"] = active_public_url
        render_html(
            f"""
<div style="background:linear-gradient(135deg,#ecfdf5,#d1fae5);border:2px solid #059669;border-radius:16px;padding:12px 14px;margin-top:8px;margin-bottom:8px;">
<div style="font-size:13.5px;font-weight:800;color:#065f46;">🌍 ลิงก์ออนไลน์ 4G/5G & ส่งเข้า LINE พร้อมใช้งาน!</div>
<div style="font-size:11.5px;color:#047857;margin-top:3px;">สแกนด้วยกล้องมือถือจากเน็ตมือถือ 4G/5G หรือคัดลอกส่งในแชต LINE ได้ทันที:</div>
<div style="font-size:12px;font-weight:800;color:#065f46;margin-top:6px;background:#ffffff;padding:6px 8px;border-radius:8px;border:1px solid #6ee7b7;word-break:break-all;">
<a href="{active_public_url}" target="_blank" style="color:#059669;text-decoration:underline;">{active_public_url}</a>
</div>
</div>
"""
        )
        pub_qr_bytes = generate_qr_code_bytes(active_public_url)
        if pub_qr_bytes:
            st.image(
                pub_qr_bytes,
                caption="🌍 สแกนเปิดดูผ่านเน็ตมือถือ 4G/5G หรือแชร์เข้า LINE ได้ทุกเครือข่าย",
                use_container_width=True,
            )

    st.markdown("---")

    # 0.15 สลับเลือกแบนเนอร์ 4K ทั้ง 12 ใบ (QR Code จริงสแกนติด 100%) & ดาวน์โหลดขึ้น MakeWebEasy
    st.markdown("### 🏆 สลับแบนเนอร์ 4K ทั้ง 12 ใบ (QR จริง 100%)")
    sb_all_12 = [f"{i:03d}" for i in range(1, 13)]
    sb_ordered_12 = ["011", "008", "012", "005", "009"] + [
        b for b in sb_all_12 if b not in ("011", "008", "012", "005", "009")
    ]
    sb_label_map = {
        "011": "🏆 011 (ชนะเลิศ • ค่าเริ่มต้นแนะนำ)",
        "008": "🏆 008 (ชนะเลิศ • สไตล์พรีเมียม)",
        "012": "🌟 012 (แนะนำ • โดดเด่นสะดุดตา)",
        "005": "🌟 005 (แนะนำ • หรูหรา)",
        "009": "🌟 009 (แนะนำ • คมชัด)",
    }

    def _on_sb_change_4k_banner() -> None:
        st.session_state["active_4k_banner_num"] = st.session_state["sb_sel_4k_banner"]
        st.session_state["ft_radio_4k_banner"] = st.session_state["sb_sel_4k_banner"]

    cur_sb_bnum = st.session_state.get("active_4k_banner_num", "011")
    if cur_sb_bnum not in sb_ordered_12:
        cur_sb_bnum = "011"

    chosen_sb_bnum = st.selectbox(
        "🎨 เลือกแบนเนอร์ 4K ที่แสดงบนหน้าเว็บแอป (001 - 012):",
        options=sb_ordered_12,
        index=sb_ordered_12.index(cur_sb_bnum),
        format_func=lambda x: sb_label_map.get(x, f"🖼️ แบบที่ {x} (Web_banner_4K_{x}.jpg)"),
        key="sb_sel_4k_banner",
        on_change=_on_sb_change_4k_banner,
    )

    enable_heavy_print_dl = st.toggle(
        "🖨️ เปิดโหลดไฟล์ต้นฉบับ 4K & โปสเตอร์ A4 300 DPI (สำหรับพี่เดย์)",
        value=False,
        key="sb_enable_heavy_print_dl",
        help="ปิดไว้เป็นค่าเริ่มต้นเพื่อให้เว็บลูกค้าโหลดเร็วภายใน 1 วินาทีและประหยัด RAM เซิร์ฟเวอร์ เมื่อพี่เดย์ต้องการโหลดไฟล์ไปปริ้นท์ให้เปิดสวิตช์นี้ครับ",
    )
    if enable_heavy_print_dl:
        sb_4k_app_bytes = get_real_qr_banner_4k_bytes(chosen_sb_bnum, "app")
        sb_4k_www_bytes = get_real_qr_banner_4k_bytes(chosen_sb_bnum, "www")
        if sb_4k_app_bytes:
            st.image(
                sb_4k_app_bytes,
                caption=f"🎯 แบนเนอร์ 4K ปัจจุบัน: Web_banner_4K_{chosen_sb_bnum}_REAL_QR.jpg (5504x3072 px)",
                use_container_width=True,
            )
            st.download_button(
                label=f"📥 ดาวน์โหลด 4K #{chosen_sb_bnum} (ชี้ไป app.dayicecream.com)",
                data=sb_4k_app_bytes,
                file_name=f"Web_banner_4K_{chosen_sb_bnum}_REAL_QR.jpg",
                mime="image/jpeg",
                use_container_width=True,
                type="primary",
                key=f"sb_dl_4k_app_{chosen_sb_bnum}",
            )
        if sb_4k_www_bytes:
            st.download_button(
                label=f"📥 ดาวน์โหลด 4K #{chosen_sb_bnum} (ชี้ไป www.dayicecream.com)",
                data=sb_4k_www_bytes,
                file_name=f"Web_banner_4K_{chosen_sb_bnum}_MAIN_WEB_QR.jpg",
                mime="image/jpeg",
                use_container_width=True,
                key=f"sb_dl_4k_www_{chosen_sb_bnum}",
            )

        st.markdown("---")

        # 0.25 ป้ายโปสเตอร์ QR Code ขนาด A4 (2480x3508 px, 300 DPI) สำหรับปริ้นท์ตั้งที่โรงงาน/หน้าร้าน
        st.markdown("### 🖨️ ป้าย QR Code สำหรับปริ้นท์ตั้งหน้าร้าน (A4 300 DPI)")
        poster_app_bytes = get_printable_a4_poster_bytes("https://app.dayicecream.com")
        poster_www_bytes = get_printable_a4_poster_bytes("https://www.dayicecream.com")
        if poster_app_bytes:
            st.download_button(
                label="📥 ดาวน์โหลดป้าย A4 300 DPI (app.dayicecream.com)",
                data=poster_app_bytes,
                file_name="QR_CODE_POSTER_FOR_PRINT.png",
                mime="image/png",
                use_container_width=True,
                type="primary",
                key="sb_dl_poster_app",
            )
        if poster_www_bytes:
            st.download_button(
                label="📥 ดาวน์โหลดป้าย A4 300 DPI (www.dayicecream.com)",
                data=poster_www_bytes,
                file_name="QR_CODE_POSTER_WWW_FOR_PRINT.png",
                mime="image/png",
                use_container_width=True,
                key="sb_dl_poster_www",
            )
        with st.expander("🖼️ ดูตัวอย่างป้ายโปสเตอร์ A4 / กำหนดลิงก์ QR Code เอง", expanded=False):
            custom_poster_url = st.text_input(
                "🔗 ลิงก์ที่ต้องการฝังใน QR Code บนโปสเตอร์ A4:",
                value=active_public_url if active_public_url else "https://app.dayicecream.com",
                key="sb_custom_poster_url",
            )
            custom_poster_bytes = get_printable_a4_poster_bytes(
                custom_poster_url.strip() or "https://app.dayicecream.com"
            )
            if custom_poster_bytes:
                st.image(
                    custom_poster_bytes,
                    caption="🖨️ ตัวอย่างป้ายโปสเตอร์ขนาด A4 แนวตั้ง (2480 x 3508 px • 300 DPI)",
                    use_container_width=True,
                )
                st.download_button(
                    label="📥 ดาวน์โหลดป้าย A4 ตามลิงก์ด้านบน (.png)",
                    data=custom_poster_bytes,
                    file_name="DAY_ICECREAM_A4_STANDEE_POSTER.png",
                    mime="image/png",
                    use_container_width=True,
                    key="sb_dl_poster_custom",
                )

    st.markdown("---")

    # 0.5 จัดการ 2 วิดีโอไวรัล & พรีเซนเทชันปิดการขาย (F:\DAY_ICECREAM_BRANCH_APP\vdo)
    st.markdown("### 🎬 จัดการ 2 วิดีโอปิดการขาย")
    with st.expander("🎥 อัปโหลดไฟล์ .mp4 / วางลิงก์ 2 วิดีโอหลัก", expanded=False):
        avail_mp4s = discover_available_mp4_files()
        mp4_options = [c["path"] for c in avail_mp4s]
        mp4_labels = {c["path"]: c["label"] for c in avail_mp4s}

        v1_data = viral_videos_cfg.get("video_1", {})
        v2_data = viral_videos_cfg.get("video_2", {})

        st.markdown("**🔴 วิดีโอที่ 1 (เปิดหัวสร้างความตะลึง — นักข่าวโลกตะลึง)**")
        cur_v1_path = v1_data.get("video_path", "")
        if cur_v1_path and cur_v1_path not in mp4_options:
            mp4_options.insert(0, cur_v1_path)
            mp4_labels[cur_v1_path] = f"📌 ปัจจุบัน: {Path(cur_v1_path).name}"
        sel_v1_path = (
            st.selectbox(
                "เลือกไฟล์ .mp4 วิดีโอที่ 1 ในเครื่อง:",
                options=mp4_options if mp4_options else [""],
                index=mp4_options.index(cur_v1_path) if (cur_v1_path in mp4_options) else 0,
                format_func=lambda x: mp4_labels.get(x, x or "(ยังไม่เลือก)"),
                key="sb_sel_v1_mp4",
            )
            if mp4_options
            else ""
        )
        up_v1_file = st.file_uploader(
            "📤 หรืออัปโหลดไฟล์ .mp4 ใหม่สำหรับวิดีโอที่ 1:",
            type=["mp4", "mov", "webm"],
            key="sb_up_v1_file",
        )
        custom_v1_url = st.text_input(
            "🔗 ลิงก์ TikTok / คลิปเต็มของวิดีโอที่ 1:",
            value=v1_data.get("external_url", "https://www.tiktok.com/@dayicecream"),
            key="sb_v1_ext_url",
        )

        st.markdown("---")
        st.markdown("**🍦 วิดีโอที่ 2 (ปิดท้ายด้วยความจริงใจ — ไอศกรีมที่จริงใจที่สุด)**")
        cur_v2_path = v2_data.get("video_path", "")
        if cur_v2_path and cur_v2_path not in mp4_options:
            mp4_options.append(cur_v2_path)
            mp4_labels[cur_v2_path] = f"📌 ปัจจุบัน: {Path(cur_v2_path).name}"
        sel_v2_path = (
            st.selectbox(
                "เลือกไฟล์ .mp4 วิดีโอที่ 2 ในเครื่อง:",
                options=mp4_options if mp4_options else [""],
                index=mp4_options.index(cur_v2_path) if (cur_v2_path in mp4_options) else 0,
                format_func=lambda x: mp4_labels.get(x, x or "(ยังไม่เลือก)"),
                key="sb_sel_v2_mp4",
            )
            if mp4_options
            else ""
        )
        up_v2_file = st.file_uploader(
            "📤 หรืออัปโหลดไฟล์ .mp4 ใหม่สำหรับวิดีโอที่ 2:",
            type=["mp4", "mov", "webm"],
            key="sb_up_v2_file",
        )
        custom_v2_url = st.text_input(
            "🔗 ลิงก์เพจ Facebook / คลิปเต็มของวิดีโอที่ 2:",
            value=v2_data.get("external_url", "https://www.facebook.com/dayicecream"),
            key="sb_v2_ext_url",
        )

        if st.button("💾 บันทึกการตั้งค่าทั้ง 2 วิดีโอ", type="primary", use_container_width=True, key="sb_save_vids_btn"):
            VDO_MAIN_DIR.mkdir(parents=True, exist_ok=True)
            PROMO_GALLERY_DIR.mkdir(parents=True, exist_ok=True)
            final_v1 = sel_v1_path
            final_v2 = sel_v2_path
            if up_v1_file is not None:
                dst1 = VDO_MAIN_DIR / up_v1_file.name
                dst1.write_bytes(up_v1_file.getvalue())
                final_v1 = str(dst1)
            if up_v2_file is not None:
                dst2 = VDO_MAIN_DIR / up_v2_file.name
                dst2.write_bytes(up_v2_file.getvalue())
                final_v2 = str(dst2)
            viral_videos_cfg["video_1"]["video_path"] = final_v1
            viral_videos_cfg["video_1"]["external_url"] = custom_v1_url.strip()
            viral_videos_cfg["video_2"]["video_path"] = final_v2
            viral_videos_cfg["video_2"]["external_url"] = custom_v2_url.strip()
            save_viral_videos_config(viral_videos_cfg)
            st.success("✅ บันทึกไฟล์และลิงก์ของทั้ง 2 วิดีโอเรียบร้อยแล้ว!")
            time.sleep(0.3)
            st.rerun()

    st.markdown("---")

    # 1. จัดการแกลเลอรีภาพโปรโมต (promo_gallery)
    st.markdown("### ⚙️ จัดการแกลเลอรีภาพโปรโมต")
    with st.expander("🖼️ อัปโหลด / แก้ไข / ลบภาพโปรโมต", expanded=False):
        uploaded_promo_files = st.file_uploader(
            "📤 เลือกไฟล์ภาพโปรโมต (อัปโหลดได้พร้อมกันหลายภาพ):",
            type=["jpg", "jpeg", "png", "webp"],
            accept_multiple_files=True,
            key="promo_gallery_uploader",
        )
        upload_mode = st.radio(
            "รูปแบบการบันทึกภาพที่อัปโหลด:",
            [
                "➕ เพิ่มเป็นภาพใหม่ในแกลเลอรี (หรือทับชื่อไฟล์เดิม)",
                "🔄 แทนที่ภาพโปรโมตลำดับที่ 1–6 ตามลำดับไฟล์",
            ],
            key="promo_upload_mode",
        )
        if st.button(
            "💾 บันทึกภาพเข้า promo_gallery",
            type="primary",
            use_container_width=True,
        ):
            if uploaded_promo_files:
                PROMO_GALLERY_DIR.mkdir(parents=True, exist_ok=True)
                items_list = promo_gallery_cfg.get("items", [])
                if upload_mode.startswith("🔄"):
                    for idx_u, uf in enumerate(uploaded_promo_files):
                        if idx_u < len(DEFAULT_PROMO_GALLERY_ITEMS):
                            target_fname = DEFAULT_PROMO_GALLERY_ITEMS[idx_u]["filename"]
                        else:
                            target_fname = uf.name
                        dst_p = PROMO_GALLERY_DIR / target_fname
                        dst_p.write_bytes(uf.getvalue())
                        if not any(it.get("filename") == target_fname for it in items_list):
                            items_list.append(
                                {
                                    "id": f"promo_{int(time.time())}_{idx_u}",
                                    "filename": target_fname,
                                    "badge": "🌟 ภาพโปรโมตเดย์ไอศครีม",
                                    "title": Path(target_fname).stem,
                                    "subtitle": "มาตรฐานไอศกรีมโฮมเมดพรีเมียม เดย์ ไอศกรีม",
                                }
                            )
                else:
                    for idx_u, uf in enumerate(uploaded_promo_files):
                        dst_p = PROMO_GALLERY_DIR / uf.name
                        dst_p.write_bytes(uf.getvalue())
                        if not any(it.get("filename") == uf.name for it in items_list):
                            items_list.append(
                                {
                                    "id": f"promo_{int(time.time())}_{idx_u}",
                                    "filename": uf.name,
                                    "badge": "🌟 ภาพโปรโมตเดย์ไอศครีม",
                                    "title": Path(uf.name).stem,
                                    "subtitle": "มาตรฐานไอศกรีมโฮมเมดพรีเมียม เดย์ ไอศกรีม",
                                }
                            )
                promo_gallery_cfg["items"] = items_list
                save_promo_gallery_config(promo_gallery_cfg)
                load_b64_image.clear()
                st.success(f"✅ บันทึกภาพ {len(uploaded_promo_files)} ไฟล์เรียบร้อย!")
                time.sleep(0.3)
                st.rerun()
            else:
                st.warning("กรุณาเลือกไฟล์ภาพก่อนกดบันทึกครับ")

        st.markdown("---")
        current_items = promo_gallery_cfg.get("items", [])
        delete_filenames = []
        for idx_g, g_item in enumerate(current_items):
            g_fname = g_item.get("filename", "")
            g_exists = (PROMO_GALLERY_DIR / g_fname).exists()
            del_chk = st.checkbox(
                f"🗑️ ลบ: #{idx_g+1} {g_fname} {'🟢' if g_exists else '⚠️'}",
                key=f"del_promo_{idx_g}_{g_fname}",
            )
            if del_chk:
                delete_filenames.append(g_fname)

        col_gal_btn1, col_gal_btn2 = st.columns(2)
        with col_gal_btn1:
            if st.button("🗑️ ลบภาพที่เลือก", use_container_width=True):
                if delete_filenames:
                    for dfn in delete_filenames:
                        fp = PROMO_GALLERY_DIR / dfn
                        if fp.exists():
                            try:
                                fp.unlink()
                            except Exception:
                                pass
                    promo_gallery_cfg["items"] = [
                        it
                        for it in current_items
                        if it.get("filename") not in delete_filenames
                    ]
                    save_promo_gallery_config(promo_gallery_cfg)
                    load_b64_image.clear()
                    st.success("✅ ลบภาพที่เลือกเรียบร้อย!")
                    time.sleep(0.3)
                    st.rerun()
        with col_gal_btn2:
            if st.button("🔄 รีเซ็ต 6 ภาพหลัก", use_container_width=True):
                promo_gallery_cfg = ensure_and_load_promo_gallery(force_reset=True)
                load_b64_image.clear()
                st.success("✅ คืนค่า 6 ภาพโปรโมตหลักเรียบร้อย!")
                time.sleep(0.3)
                st.rerun()

    st.divider()

    # 2. จัดการสต็อก 30 รสชาติ
    st.markdown("### 🍨 จัดการสต็อก 30 รสชาติ")
    with st.expander("📦 เปิด/ปิด รสชาติที่สินค้าหมด (30 รสชาติ)", expanded=False):
        stock_selections = {}
        for flv in flavors_cfg.get("flavors", []):
            fid = flv["id"]
            is_oos = st.checkbox(
                f"❌ หมด: #{fid:02d} {flv['name']}",
                value=bool(flv.get("out_of_stock", False)),
                key=f"admin_oos_{fid}",
            )
            stock_selections[fid] = is_oos

        if st.button("💾 บันทึกสถานะสต็อก 30 รสชาติ", type="primary", use_container_width=True):
            for flv in flavors_cfg.get("flavors", []):
                fid = flv["id"]
                flv["out_of_stock"] = bool(stock_selections.get(fid, False))
                if flv["out_of_stock"]:
                    st.session_state[f"qty_flv_{fid}"] = 0
            save_flavors_config(flavors_cfg)
            st.success("✅ บันทึกสถานะสต็อกเรียบร้อยแล้ว!")
            time.sleep(0.3)
            st.rerun()

    st.divider()

    # 3. โหมดหลังบ้านดูหมุดสถานะภายใน & สถิติหมุดจริง (แสดงเฉพาะใน Sidebar สำหรับพี่เดย์เท่านั้น ลูกค้าไม่เห็น)
    st.markdown("### 🗺️ ตั้งค่าแผนที่สาขา (สำหรับพี่เดย์)")
    total_pins_backend = len(all_branches)
    public_pins_backend = sum(1 for b in all_branches if not b.get("is_internal"))
    internal_pins_backend = sum(1 for b in all_branches if b.get("is_internal"))
    smart_customer_label_preview = (
        "กว่า 300+ สาขาทั่วประเทศไทย"
        if public_pins_backend <= 300
        else f"{public_pins_backend:,} สาขาทั่วประเทศไทย"
    )
    render_html(
        f"""
<div style="background:#FFFBF5;border:1.5px solid #fca5a5;border-radius:14px;padding:12px 14px;margin-bottom:10px;font-size:12.5px;color:#2B1810;line-height:1.55;">
<div style="color:#b71c1c;font-weight:800;font-size:13.5px;margin-bottom:4px;">📊 สถิติหมุดจริงหลังบ้าน (เฉพาะพี่เดย์)</div>
<div>• หมุดทั้งหมดในระบบ: <b>{total_pins_backend} หมุด</b></div>
<div>• เปิดบริการลูกค้าทั่วไป: <b style="color:#15803d;">{public_pins_backend} สาขา</b></div>
<div>• หมุดสถานะภายใน (จอง/เก็บตู้/ยกเลิก): <b style="color:#d32f2f;">{internal_pins_backend} หมุด</b></div>
<div style="margin-top:4px;padding-top:4px;border-top:1px dashed #fca5a5;color:#5C4033;">
✨ หน้าเว็บลูกค้าแสดงผล: <b style="color:#d32f2f;">{smart_customer_label_preview}</b>
</div>
</div>
"""
    )
    admin_mode = st.toggle(
        "🔓 แสดงหมุดสถานะภายใน (จอง/เก็บตู้/ยกเลิก)",
        value=False,
        help="สำหรับพี่เดย์ตรวจสอบหมุดจอง/เก็บตู้/ยกเลิก (ลูกค้าทั่วไปจะไม่เห็นหมุดเหล่านี้)",
    )
    col_sync1, col_sync2 = st.columns(2)
    with col_sync1:
        if st.button("🔄 อัปเดตลิงก์", use_container_width=True):
            links_cfg = sync_linktree_links(force=True)
            st.toast("✅ อัปเดตลิงก์โซเชียลเรียบร้อย!", icon="✨")
            st.rerun()
    with col_sync2:
        if st.button("🔄 อัปเดตสาขา", use_container_width=True):
            load_branches_live.clear()
            all_branches, branches_sync_status = load_branches_live(force_refresh=True)
            build_thailand_branch_map.clear()
            st.toast("✅ อัปเดตข้อมูลสาขาล่าสุดเรียบร้อย!", icon="📍")
            st.rerun()

    st.divider()

    # 4. ตั้งค่า/เพิ่มลิงก์ช่อง YouTube ในเครือ DAY STUDIO
    st.markdown("### 🎬 ตั้งค่าลิงก์ช่อง DAY STUDIO")
    with st.expander("⚙️ แก้ไขลิงก์ช่อง YouTube", expanded=False):
        updated_channels = []
        for idx, ch in enumerate(channels_cfg.get("channels", [])):
            st.markdown(f"**{ch.get('icon', '🎬')} {ch.get('name', '')}**")
            new_name = st.text_input(
                f"ชื่อช่อง #{idx+1}",
                value=ch.get("name", ""),
                key=f"ch_name_{idx}",
            )
            new_sub = st.text_input(
                f"คำโปรย #{idx+1}",
                value=ch.get("subtitle", ""),
                key=f"ch_sub_{idx}",
            )
            new_url = st.text_input(
                f"ลิงก์ช่อง ({ch.get('name', '')})",
                value=ch.get("url", ""),
                placeholder="https://www.youtube.com/@... (เว้นว่าง = เร็วๆ นี้)",
                key=f"ch_url_{idx}",
            )
            new_btn_txt = st.text_input(
                f"ข้อความบนปุ่ม ({ch.get('name', '')})",
                value=ch.get("button_text", f"▶️ เข้าชมและกดติดตามช่อง {ch.get('name', '')}"),
                key=f"ch_btn_{idx}",
            )
            updated_ch = dict(ch)
            updated_ch["name"] = new_name.strip()
            updated_ch["subtitle"] = new_sub.strip()
            updated_ch["url"] = new_url.strip()
            updated_ch["button_text"] = new_btn_txt.strip()
            updated_channels.append(updated_ch)
            st.markdown("---")

        if st.button("💾 บันทึกลิงก์ช่อง", type="primary", use_container_width=True):
            channels_cfg["channels"] = updated_channels
            save_channels_config(channels_cfg)
            st.success("✅ บันทึกการตั้งค่าช่องเรียบร้อย!")
            time.sleep(0.3)
            st.rerun()

    with st.expander("➕ เพิ่มช่องใหม่", expanded=False):
        add_icon = st.text_input("ไอคอน", value="🌟", key="add_ch_icon")
        add_name = st.text_input("ชื่อช่องใหม่", placeholder="เช่น DAY WONDER KIDS", key="add_ch_name")
        add_sub = st.text_input("คำโปรย", placeholder="สโลแกนช่อง...", key="add_ch_sub")
        add_desc = st.text_area("รายละเอียด", placeholder="คำอธิบายช่อง...", key="add_ch_desc", height=68)
        add_url = st.text_input("ลิงก์ URL", placeholder="https://www.youtube.com/@...", key="add_ch_url")
        add_btn = st.text_input("ข้อความปุ่มกด", value="▶️ เข้าชมและกดติดตามช่อง", key="add_ch_btn")
        if st.button("➕ เพิ่มช่องและบันทึก", use_container_width=True):
            if add_name.strip():
                channels_cfg.setdefault("channels", []).append(
                    {
                        "id": f"custom_{int(time.time())}",
                        "icon": add_icon.strip() or "🎬",
                        "name": add_name.strip(),
                        "subtitle": add_sub.strip() or "ช่องคุณภาพในเครือ DAY STUDIO",
                        "description": add_desc.strip() or add_sub.strip() or "ช่องคุณภาพในเครือ DAY STUDIO",
                        "url": add_url.strip(),
                        "button_text": add_btn.strip() or f"▶️ เข้าชมและกดติดตามช่อง {add_name.strip()}",
                        "badge_coming_soon": "⏳ เร็วๆ นี้ (Coming Soon)",
                        "accent_color": "#d32f2f",
                        "logo_key": "day_gold_coin",
                    }
                )
                save_channels_config(channels_cfg)
                st.success(f"✅ เพิ่มช่อง '{add_name.strip()}' เรียบร้อย!")
                time.sleep(0.3)
                st.rerun()


# ==============================================================================
# GLOBAL CSS: SWENSEN'S / KFC MODERN CREAMY VANILLA & SIGNATURE RED THEME
# ==============================================================================
render_html(
    """
    <style>
        @import url('https://fonts.googleapis.com/css2?family=Kanit:wght@300;400;500;600;700;800&family=Prompt:wght@300;400;500;600;700;800&display=swap');

        /* ซ่อนแถบ Header/Footer มาตรฐานของ Streamlit เพื่อไม่ให้มีปุ่ม Deploy หรือเมนูรกตา */
        #MainMenu, header, footer {
            visibility: hidden !important;
        }
        .stDeployButton,
        [data-testid="stToolbar"],
        [data-testid="stDecoration"],
        [data-testid="stStatusWidget"] {
            display: none !important;
        }
        /* คงปุ่มเปิดแถบตั้งค่าซ้ายมือไว้เฉพาะมุมบนซ้ายอย่างแนบเนียนสำหรับพี่เดย์ */
        [data-testid="collapsedControl"],
        [data-testid="stSidebarCollapsedControl"] {
            visibility: visible !important;
            opacity: 0.45;
            transition: opacity 0.2s ease;
        }
        [data-testid="collapsedControl"]:hover,
        [data-testid="stSidebarCollapsedControl"]:hover {
            opacity: 1.0;
        }

        /* พื้นหลังหลักสีครีมนมสดอบอุ่น (#FFFBF5) และฟอนต์ Prompt / Kanit */
        html, body, .stApp, [data-testid="stAppViewContainer"], [class*="css"] {
            font-family: 'Prompt', 'Kanit', sans-serif !important;
            background-color: #FFFBF5 !important;
            color: #2B1810 !important;
        }

        .block-container {
            padding-top: 1.0rem !important;
            padding-bottom: 3.5rem !important;
            max-width: 1420px !important;
        }

        /* ตกแต่ง st.container(border=True) ให้เป็นกรอบการ์ดสีขาวครีมสุดหรูสไตล์ Swensen's / KFC */
        div[data-testid="stVerticalBlockBorderWrapper"] {
            background: #FFFFFF !important;
            border: 1.5px solid #f1dfcf !important;
            border-radius: 18px !important;
            padding: 12px 14px !important;
            box-shadow: 0 6px 18px rgba(211, 47, 47, 0.07) !important;
            transition: all 0.2s ease !important;
        }
        div[data-testid="stVerticalBlockBorderWrapper"]:hover {
            border-color: #ff5252 !important;
            box-shadow: 0 10px 24px rgba(211, 47, 47, 0.15) !important;
        }
        div[data-testid="stImage"] img {
            border-radius: 12px !important;
            object-fit: cover !important;
        }

        /* แบนเนอร์หัวเว็บซิกเนเจอร์สีแดงสด Day Ice Cream */
        .brand-hero-banner {
            background: linear-gradient(135deg, #d32f2f 0%, #e53935 55%, #ff5252 100%);
            border-radius: 22px;
            padding: 24px 30px;
            margin-bottom: 18px;
            box-shadow: 0 10px 28px rgba(211, 47, 47, 0.18);
            border: 2px solid #fecaca;
            display: flex;
            align-items: center;
            justify-content: space-between;
            flex-wrap: wrap;
            gap: 18px;
            color: #ffffff !important;
        }
        /* หัวเว็บสไตล์ Swensen's (Mobile-First Clean Cream & Signature Red Header) */
        .swensens-header-card {
            background: linear-gradient(180deg, #FFFFFF 0%, #FFFDF9 100%);
            border: 2px solid #fecaca;
            border-top: 8px solid #d32f2f;
            border-radius: 24px;
            padding: 20px 18px 18px 18px;
            margin-bottom: 14px;
            text-align: center;
            box-shadow: 0 10px 28px rgba(211, 47, 47, 0.10);
        }
        .swensens-logo-img {
            width: 200px;
            max-width: 72%;
            height: auto;
            border-radius: 18px;
            border: 2.5px solid #ffe4e6;
            background: #ffffff;
            padding: 6px 12px;
            box-shadow: 0 6px 18px rgba(211, 47, 47, 0.14);
            display: block;
            margin: 0 auto 10px auto;
        }
        .swensens-brand-title {
            font-family: 'Kanit', 'Prompt', sans-serif !important;
            font-size: 26px;
            font-weight: 800;
            color: #b71c1c !important;
            margin: 2px 0 4px 0;
            line-height: 1.25;
        }
        .swensens-brand-slogan {
            font-size: 14.5px;
            font-weight: 700;
            color: #5C4033 !important;
            margin: 0 0 12px 0;
            line-height: 1.4;
        }
        .swensens-badges-grid {
            display: flex;
            flex-wrap: wrap;
            justify-content: center;
            gap: 8px;
            margin-bottom: 14px;
        }
        .swensens-gold-badge {
            background: #FFFDF7;
            color: #b71c1c !important;
            border: 1.5px solid #f59e0b;
            border-radius: 999px;
            padding: 6px 13px;
            font-size: 13px;
            font-weight: 800;
            box-shadow: 0 3px 10px rgba(245, 158, 11, 0.12);
            display: inline-flex;
            align-items: center;
            gap: 5px;
        }
        .swensens-hotline-row {
            display: grid;
            grid-template-columns: 1fr 1fr;
            gap: 10px;
            max-width: 540px;
            margin: 0 auto;
        }
        .swensens-call-btn {
            display: flex;
            align-items: center;
            justify-content: center;
            gap: 6px;
            background: linear-gradient(135deg, #d32f2f, #ef4444);
            color: #ffffff !important;
            font-weight: 800;
            font-size: 14.5px;
            padding: 11px 12px;
            border-radius: 14px;
            text-decoration: none !important;
            box-shadow: 0 5px 14px rgba(211, 47, 47, 0.24);
        }
        .swensens-line-btn {
            display: flex;
            align-items: center;
            justify-content: center;
            gap: 6px;
            background: linear-gradient(135deg, #059669, #10b981);
            color: #ffffff !important;
            font-weight: 800;
            font-size: 14.5px;
            padding: 11px 12px;
            border-radius: 14px;
            text-decoration: none !important;
            box-shadow: 0 5px 14px rgba(5, 150, 105, 0.24);
        }

        /* ปุ่มเมนูหลักขนาดใหญ่บนหน้าจอมือถือ (Mobile Action Navigation Grid) */
        div.stButton > button {
            width: 100% !important;
            white-space: normal !important;
            word-wrap: break-word !important;
            height: auto !important;
            min-height: 56px !important;
            padding: 12px 16px !important;
            border-radius: 16px !important;
            font-family: 'Kanit', 'Prompt', sans-serif !important;
            font-size: 15.5px !important;
            font-weight: 800 !important;
            line-height: 1.38 !important;
            transition: all 0.18s ease !important;
        }
        div.stButton > button p {
            font-family: 'Kanit', 'Prompt', sans-serif !important;
            font-size: 15.5px !important;
            font-weight: 800 !important;
            line-height: 1.38 !important;
            white-space: normal !important;
        }
        div.stButton > button[kind="primary"] {
            background: linear-gradient(135deg, #d32f2f 0%, #ef4444 100%) !important;
            color: #ffffff !important;
            border: 2.5px solid #fde047 !important;
            box-shadow: 0 8px 20px rgba(211, 47, 47, 0.28) !important;
        }
        div.stButton > button[kind="primary"] p {
            color: #ffffff !important;
        }
        div.stButton > button[kind="secondary"] {
            background: #FFFFFF !important;
            color: #b71c1c !important;
            border: 2px solid #fca5a5 !important;
            box-shadow: 0 4px 14px rgba(211, 47, 47, 0.08) !important;
        }
        div.stButton > button[kind="secondary"] p {
            color: #b71c1c !important;
        }
        div.stButton > button[kind="secondary"]:hover {
            background: #fff1f2 !important;
            border-color: #d32f2f !important;
            transform: translateY(-1px);
        }

        /* การ์ดและแบนเนอร์หัวข้อโซน (Creamy Vanilla & Signature Red) */
        .brand-section-header {
            background: linear-gradient(135deg, #d32f2f, #ff5252);
            color: #ffffff !important;
            border-radius: 18px;
            padding: 16px 24px;
            margin: 14px 0 18px 0;
            box-shadow: 0 8px 24px rgba(211, 47, 47, 0.12);
            display: flex;
            align-items: center;
            justify-content: space-between;
            flex-wrap: wrap;
            gap: 12px;
        }
        .brand-section-title {
            font-family: 'Kanit', 'Prompt', sans-serif !important;
            font-size: 22px;
            font-weight: 800;
            color: #ffffff !important;
            margin: 0;
        }
        .brand-section-sub {
            color: #fffbeb !important;
            font-size: 13.8px;
            margin-top: 3px;
        }

        /* การ์ดมาตรฐานสีครีม-ขาวสะอาดตา */
        .cream-card {
            background: #FFFFFF;
            border: 1.5px solid #f3dfd3;
            border-radius: 18px;
            padding: 18px 20px;
            box-shadow: 0 8px 24px rgba(211, 47, 47, 0.07);
            transition: all 0.2s ease;
        }
        .cream-card:hover {
            border-color: #ff5252;
            box-shadow: 0 12px 28px rgba(211, 47, 47, 0.14);
            transform: translateY(-2px);
        }

        /* การ์ดโปรโมชันสีแดงสดซิกเนเจอร์ */
        .promo-red-card {
            background: linear-gradient(135deg, #d32f2f, #ff5252);
            color: #ffffff !important;
            border-radius: 18px;
            padding: 20px 24px;
            box-shadow: 0 8px 24px rgba(211, 47, 47, 0.16);
        }

        /* การ์ดปุ่มลัดโซเชียล */
        .cta-grid {
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(280px, 1fr));
            gap: 12px;
            margin-bottom: 12px;
        }
        .cta-card {
            display: flex;
            align-items: center;
            gap: 14px;
            padding: 14px 18px;
            border-radius: 18px;
            text-decoration: none !important;
            transition: all 0.22s ease;
            box-shadow: 0 8px 24px rgba(211, 47, 47, 0.12);
        }
        .cta-card:hover {
            transform: translateY(-2px);
            box-shadow: 0 12px 28px rgba(211, 47, 47, 0.22);
        }
        .cta-promo {
            background: linear-gradient(135deg, #d32f2f, #ff5252);
            color: #ffffff !important;
        }
        .cta-line {
            background: linear-gradient(135deg, #059669, #10b981);
            color: #ffffff !important;
        }
        .cta-web {
            background: linear-gradient(135deg, #ea580c, #f97316);
            color: #ffffff !important;
        }
        .cta-thumb {
            width: 52px;
            height: 52px;
            border-radius: 14px;
            object-fit: cover;
            border: 2px solid #ffffff;
            flex-shrink: 0;
            background: #fff;
        }
        .cta-title {
            font-size: 15px;
            font-weight: 800;
            line-height: 1.35;
            color: #ffffff !important;
        }
        .cta-url {
            font-size: 12px;
            color: rgba(255, 255, 255, 0.92) !important;
            margin-top: 3px;
        }

        .social-row {
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(220px, 1fr));
            gap: 10px;
            margin-top: 8px;
        }
        .social-pill {
            display: flex;
            align-items: center;
            justify-content: space-between;
            padding: 12px 16px;
            border-radius: 14px;
            background: #FFFFFF;
            border: 1.5px solid #f3dfd3;
            color: #2B1810 !important;
            text-decoration: none !important;
            font-weight: 700;
            font-size: 13.5px;
            box-shadow: 0 4px 14px rgba(211, 47, 47, 0.06);
            transition: all 0.2s ease;
        }
        .social-pill:hover {
            border-color: #d32f2f;
            background: #fff5f5;
            transform: translateY(-2px);
        }

        /* การ์ดสาขา (Compact Clean Design — ไม่มีกรอบรูปภาพ) */
        .branch-card {
            background: #FFFFFF;
            border: 1.5px solid #f1dfcf;
            border-radius: 18px;
            padding: 16px;
            height: 100%;
            display: flex;
            flex-direction: column;
            justify-content: space-between;
            box-shadow: 0 6px 20px rgba(211, 47, 47, 0.08);
            transition: all 0.2s ease;
        }
        .branch-card:hover {
            border-color: #d32f2f;
            box-shadow: 0 10px 26px rgba(211, 47, 47, 0.15);
            transform: translateY(-2px);
        }
        .branch-card-internal {
            border: 2px dashed #d32f2f !important;
            background: #fff5f5 !important;
        }
        .branch-actions-row {
            display: grid;
            grid-template-columns: 1fr 1.25fr;
            gap: 8px;
            margin-top: 12px;
        }
        .branch-call-btn {
            display: flex;
            align-items: center;
            justify-content: center;
            gap: 5px;
            width: 100%;
            text-align: center;
            background: linear-gradient(135deg, #059669, #10b981);
            color: #ffffff !important;
            font-weight: 800;
            font-size: 13.5px;
            padding: 11px 10px;
            border-radius: 12px;
            text-decoration: none !important;
            box-shadow: 0 5px 14px rgba(5, 150, 105, 0.24);
            transition: all 0.2s ease;
        }
        .branch-call-btn:hover {
            background: linear-gradient(135deg, #047857, #059669);
            transform: translateY(-1px);
        }
        .branch-nav-btn, .nav-btn {
            display: flex;
            align-items: center;
            justify-content: center;
            gap: 5px;
            width: 100%;
            text-align: center;
            background: linear-gradient(135deg, #d32f2f, #ff5252);
            color: #ffffff !important;
            font-weight: 800;
            font-size: 13.5px;
            padding: 11px 10px;
            border-radius: 12px;
            text-decoration: none !important;
            box-shadow: 0 5px 14px rgba(211, 47, 47, 0.24);
            transition: all 0.2s ease;
        }
        .branch-nav-btn:hover, .nav-btn:hover {
            background: linear-gradient(135deg, #b71c1c, #d32f2f);
            box-shadow: 0 8px 20px rgba(211, 47, 47, 0.35);
            transform: translateY(-1px);
        }

        /* การ์ดช่อง YouTube DAY STUDIO */
        .studio-card {
            background: #FFFFFF;
            border: 2px solid #f3dfd3;
            border-radius: 18px;
            padding: 22px 20px;
            height: 100%;
            display: flex;
            flex-direction: column;
            justify-content: space-between;
            box-shadow: 0 8px 24px rgba(211, 47, 47, 0.09);
        }
        .yt-red-btn {
            display: block;
            width: 100%;
            text-align: center;
            background: linear-gradient(135deg, #d32f2f, #ff5252);
            color: #ffffff !important;
            font-weight: 800;
            font-size: 15px;
            padding: 13px 16px;
            border-radius: 12px;
            text-decoration: none !important;
            box-shadow: 0 6px 18px rgba(211, 47, 47, 0.25);
            transition: all 0.2s ease;
        }
        .yt-red-btn:hover {
            transform: translateY(-2px);
            box-shadow: 0 10px 24px rgba(211, 47, 47, 0.38);
        }
        .coming-soon-badge {
            display: block;
            width: 100%;
            text-align: center;
            background: #FFF8EE;
            color: #d97706 !important;
            font-weight: 800;
            font-size: 14.5px;
            padding: 13px 16px;
            border-radius: 12px;
            border: 1.5px dashed #f59e0b;
        }

        /* การ์ดดีลเลอร์ประจำจังหวัด */
        .dealer-cards-grid {
            display: grid;
            grid-template-columns: repeat(4, minmax(0, 1fr));
            gap: 16px;
            align-items: stretch;
            margin-top: 6px;
            margin-bottom: 14px;
        }
        @media (max-width: 1100px) {
            .dealer-cards-grid {
                grid-template-columns: repeat(2, minmax(0, 1fr));
            }
        }
        @media (max-width: 640px) {
            .dealer-cards-grid {
                grid-template-columns: 1fr;
            }
        }
        .dealer-card {
            background: #FFFFFF;
            border: 2px solid #fecaca;
            border-radius: 18px;
            padding: 18px;
            height: 100%;
            display: flex;
            flex-direction: column;
            justify-content: space-between;
            box-shadow: 0 8px 24px rgba(211, 47, 47, 0.08);
            box-sizing: border-box;
        }

        /* ปุ่ม + / - เลือกจำนวนถ้วยไอศกรีมขนาดใหญ่ กดง่ายด้วยนิ้วโป้งเหมือนแอป KFC / Swensen's */
        div[data-testid="stNumberInput"] div[data-baseweb="input"] {
            border-radius: 12px !important;
            border: 2px solid #fca5a5 !important;
            background: #fffafa !important;
        }
        div[data-testid="stNumberInput"] input {
            font-size: 18px !important;
            font-weight: 800 !important;
            color: #b71c1c !important;
            text-align: center !important;
            min-height: 44px !important;
        }
        div[data-testid="stNumberInput"] button,
        button[data-testid="stNumberInputStepDown"],
        button[data-testid="stNumberInputStepUp"] {
            min-width: 44px !important;
            min-height: 44px !important;
            font-size: 20px !important;
            font-weight: 900 !important;
            background: linear-gradient(135deg, #d32f2f 0%, #ef4444 100%) !important;
            color: #ffffff !important;
            border-radius: 10px !important;
            border: none !important;
            margin: 2px !important;
            box-shadow: 0 3px 8px rgba(211, 47, 47, 0.22) !important;
            transition: transform 0.12s ease !important;
        }
        div[data-testid="stNumberInput"] button:active {
            transform: scale(0.94) !important;
        }
        div[data-testid="stNumberInput"] button svg {
            fill: #ffffff !important;
            stroke: #ffffff !important;
            width: 18px !important;
            height: 18px !important;
        }

        /* ============================================================================
           📱 MOBILE-FIRST RESPONSIVE OPTIMIZATION (@media max-width: 768px)
           ปรับขนาดฟอนต์ ปุ่มกด การ์ดไอศกรีม 30 รสชาติ และเครื่องคิดเลขกำไรแฟรนไชส์ให้พอดีจอมือถือ 100%
           ============================================================================ */
        @media (max-width: 768px) {
            html, body, .stApp {
                overflow-x: hidden !important;
            }
            .block-container {
                padding-top: 0.45rem !important;
                padding-bottom: 2.2rem !important;
                padding-left: 0.65rem !important;
                padding-right: 0.65rem !important;
                max-width: 100% !important;
            }
            .swensens-header-card {
                padding: 16px 12px 14px 12px !important;
                border-radius: 20px !important;
            }
            .swensens-logo-img {
                width: 195px !important;
                max-width: 78% !important;
            }
            .swensens-brand-title {
                font-size: 21px !important;
                line-height: 1.25 !important;
            }
            .swensens-brand-slogan {
                font-size: 13px !important;
                line-height: 1.38 !important;
            }
            .swensens-gold-badge {
                font-size: 12px !important;
                padding: 5px 10px !important;
                width: 100% !important;
                justify-content: center !important;
            }
            .swensens-call-btn, .swensens-line-btn {
                font-size: 13.5px !important;
                padding: 10px 8px !important;
            }
            /* ปุ่มเมนูหลักทุกปุ่มบนมือถือ: เต็มจอ ไม่ตัดขอบ กดง่ายด้วยนิ้วโป้ง */
            div.stButton > button {
                min-height: 54px !important;
                font-size: 14.8px !important;
                padding: 11px 13px !important;
                border-radius: 15px !important;
                white-space: normal !important;
                height: auto !important;
            }
            div.stButton > button p {
                font-size: 14.8px !important;
                line-height: 1.35 !important;
                white-space: normal !important;
            }
            /* ปุ่ม + / - เลือกจำนวนถ้วยไอศกรีมบนจอมือถือ ใหญ่พิเศษแบบแอป KFC / Swensen's */
            div[data-testid="stNumberInput"] input {
                font-size: 20px !important;
                min-height: 48px !important;
            }
            div[data-testid="stNumberInput"] button,
            button[data-testid="stNumberInputStepDown"],
            button[data-testid="stNumberInputStepUp"] {
                min-width: 48px !important;
                min-height: 48px !important;
                font-size: 22px !important;
                border-radius: 12px !important;
            }
            /* การ์ดไอศกรีม 30 รสชาติ & การ์ดสาขาบนมือถือ */
            div[data-testid="stVerticalBlockBorderWrapper"] {
                border-radius: 16px !important;
                padding: 10px !important;
                margin-bottom: 8px !important;
            }
            .branch-card, .dealer-card, .promo-card, .pkg-card {
                padding: 14px !important;
                border-radius: 16px !important;
            }
            .brand-section-header {
                padding: 14px 16px !important;
                border-radius: 16px !important;
            }
            .brand-section-title {
                font-size: 18px !important;
                line-height: 1.3 !important;
            }
            .brand-section-sub {
                font-size: 12.5px !important;
                line-height: 1.4 !important;
            }
        }
    </style>
    """
)


# ==============================================================================
# MODAL DIALOG FOR FULL-HD PROMO GALLERY ZOOM
# ==============================================================================
if hasattr(st, "dialog"):

    @st.dialog("🔍 ภาพโปรโมตขนาดใหญ่คมชัด (Full HD)", width="large")
    def show_promo_zoom_dialog(
        img_path_str: str, title_str: str, sub_str: str, badge_str: str
    ) -> None:
        render_html(
            f"""
<div style="background:linear-gradient(135deg,#d32f2f,#ff5252);border-radius:14px;padding:14px 18px;margin-bottom:12px;color:#ffffff;">
<span style="background:#ffffff;color:#d32f2f;font-size:11.5px;font-weight:800;padding:3px 10px;border-radius:99px;">{badge_str}</span>
<div style="font-size:18px;font-weight:800;margin-top:6px;">{title_str}</div>
<div style="font-size:13.5px;margin-top:4px;opacity:0.95;">{sub_str}</div>
</div>
"""
        )
        st.image(img_path_str, use_container_width=True)
else:
    show_promo_zoom_dialog = None


# ==============================================================================
# 🎠 1. AUTO-SLIDING HERO CAROUSEL (SWENSEN'S STYLE • 3 ภาพคมชัดเต็มจอ ไร้ตัวหนังสือบังรูป!)
# ==============================================================================
@st.cache_data(max_entries=1, show_spinner=False)
def prepare_and_load_hero_slides_3cups() -> list[dict]:
    """
    นำไฟล์ภาพ 3 ถ้วยซิกเนเจอร์ที่คมชัดที่สุด 3 ภาพ (150.jpg, 200.jpg, 100.jpg)
    ครอปขอบซ้าย-ขวาที่ว่างเปล่าออกเล็กน้อยให้ได้สัดส่วน 16:10 (1120x700) เพื่อให้ถ้วยไอศกรีมทั้ง 3 ถ้วย
    ขยายใหญ่เต็มจอมือถือ ดูน่ากินสุดๆ โหลดไวภายในเสี้ยววินาที และลบสไลด์ใบที่ 4 ออกถาวร
    """
    PROMO_GALLERY_DIR.mkdir(parents=True, exist_ok=True)
    old_slide_4 = PROMO_GALLERY_DIR / "slide_4.jpg"
    if old_slide_4.exists():
        try:
            old_slide_4.unlink()
        except Exception:
            pass

    slide_specs = [
        {"src_name": "150.jpg", "dst_name": "slide_1.jpg"},
        {"src_name": "200.jpg", "dst_name": "slide_2.jpg"},
        {"src_name": "100.jpg", "dst_name": "slide_3.jpg"},
    ]
    loaded_slides = []
    for sp in slide_specs:
        src_path = APP_DIR / sp["src_name"]
        dst_path = PROMO_GALLERY_DIR / sp["dst_name"]
        need_crop = (
            src_path.exists()
            and (not dst_path.exists() or dst_path.stat().st_size > 165 * 1024)
        )
        if need_crop:
            try:
                from PIL import Image

                with Image.open(src_path) as raw_im:
                    img = raw_im.convert("RGB")
                w, h = img.size
                target_ratio = 16.0 / 10.0
                new_w = int(h * target_ratio)
                if new_w < w:
                    left = (w - new_w) // 2
                    img = img.crop((left, 0, left + new_w, h))
                img.resize((1120, 700), Image.Resampling.LANCZOS).save(
                    dst_path, "JPEG", quality=82, optimize=True
                )
            except Exception:
                if not dst_path.exists():
                    try:
                        shutil.copy2(src_path, dst_path)
                    except Exception:
                        pass
        target_file = dst_path if dst_path.exists() else src_path
        if target_file.exists():
            try:
                b64_data = base64.b64encode(target_file.read_bytes()).decode("ascii")
                loaded_slides.append(
                    {
                        "b64": b64_data,
                        "dst_name": sp["dst_name"],
                    }
                )
            except Exception:
                pass
    return loaded_slides


HERO_SLIDES_DATA = prepare_and_load_hero_slides_3cups()

main_logo_html = (
    f'<img src="data:image/jpeg;base64,{HEADER_MAIN_LOGO_B64}" style="height:54px;width:auto;border-radius:12px;border:2px solid #fecaca;background:#fff;padding:3px 8px;box-shadow:0 4px 12px rgba(211,47,47,0.14);" alt="Day Ice Cream Logo" />'
    if HEADER_MAIN_LOGO_B64
    else '<span style="font-size:36px;">🍦</span>'
)

# แถบโลโก้และปุ่มโทร/LINE สไตล์ Swensen's ด้านบนสไลด์โชว์
render_html(
    f"""
<div style="background:#FFFFFF;border:2px solid #fecaca;border-top:6px solid #d32f2f;border-radius:20px;padding:10px 16px;margin-bottom:8px;display:flex;align-items:center;justify-content:space-between;flex-wrap:wrap;gap:10px;box-shadow:0 6px 20px rgba(211,47,47,0.08);">
<div style="display:flex;align-items:center;gap:12px;">
{main_logo_html}
<div>
<div style="font-family:'Kanit','Prompt',sans-serif;font-size:20px;font-weight:800;color:#b71c1c;line-height:1.2;">เดย์ ไอศกรีม (DAY ICE CREAM)</div>
<div style="font-size:12.5px;font-weight:700;color:#5C4033;">ความสุขที่คุณสัมผัสได้ • ไอศกรีมโฮมเมดแท้ 100% Organic</div>
</div>
</div>
<div style="display:flex;gap:8px;flex-wrap:wrap;">
<a href="tel:0863328091" style="background:linear-gradient(135deg,#d32f2f,#ef4444);color:#ffffff;font-weight:800;font-size:13px;padding:8px 14px;border-radius:999px;text-decoration:none;box-shadow:0 4px 12px rgba(211,47,47,0.22);">📞 โทร: 086-3328091</a>
<a href="https://line.me/ti/p/BX7Fscqs71" target="_blank" rel="noopener noreferrer" style="background:linear-gradient(135deg,#059669,#10b981);color:#ffffff;font-weight:800;font-size:13px;padding:8px 14px;border-radius:999px;text-decoration:none;box-shadow:0 4px 12px rgba(5,150,105,0.22);">💬 LINE: Dayinterfood</a>
</div>
</div>
"""
)

# สร้าง Auto-Sliding Hero Carousel 3 ภาพคมชัด (ห้ามวางป้ายข้อความทับบนรูปภาพเด็ดขาด! + แถบแคปซูลวางไว้นอกกรอบรูปด้านล่าง + ไร้ช่องว่างสีขาวคั่นกลาง)
if HERO_SLIDES_DATA:
    slides_dom_items = []
    dots_dom_items = []
    for s_idx, s_item in enumerate(HERO_SLIDES_DATA):
        active_cls = " active" if s_idx == 0 else ""
        slides_dom_items.append(
            f"""
            <div class="hero-slide{active_cls}" data-index="{s_idx}">
                <img src="data:image/jpeg;base64,{s_item['b64']}" alt="Day Ice Cream Signature Slide {s_idx + 1}" />
            </div>
            """
        )
        dots_dom_items.append(
            f'<button type="button" class="hero-dot{active_cls}" data-slide="{s_idx}" aria-label="Slide {s_idx + 1}"></button>'
        )

    hero_carousel_html = f"""
    <style>
        .day-hero-wrapper {{
            width: 100%;
            margin: 0 0 6px 0;
            padding: 0;
            font-family: 'Kanit', 'Prompt', sans-serif;
        }}
        #hero-carousel-root {{
            position: relative;
            width: 100%;
            aspect-ratio: 16 / 9;
            max-height: 460px;
            border-radius: 22px;
            overflow: hidden;
            border: 3px solid #fca5a5;
            box-shadow: 0 10px 26px rgba(211, 47, 47, 0.16);
            background: #1a0d08;
            user-select: none;
        }}
        .hero-slide {{
            position: absolute;
            inset: 0;
            opacity: 0;
            transform: scale(1.015);
            transition: opacity 0.6s ease-in-out, transform 0.6s ease-in-out;
            pointer-events: none;
        }}
        .hero-slide.active {{
            opacity: 1;
            transform: scale(1);
            pointer-events: auto;
            z-index: 2;
        }}
        .hero-slide img {{
            width: 100%;
            height: 100%;
            object-fit: cover;
            object-position: center center;
            display: block;
        }}
        .hero-nav-btn {{
            position: absolute;
            top: 50%;
            transform: translateY(-50%);
            z-index: 8;
            width: 40px;
            height: 40px;
            border-radius: 50%;
            background: rgba(211, 47, 47, 0.85);
            color: #ffffff;
            border: 2px solid #fde047;
            font-size: 18px;
            font-weight: 900;
            cursor: pointer;
            display: flex;
            align-items: center;
            justify-content: center;
            box-shadow: 0 4px 12px rgba(0, 0, 0, 0.38);
            transition: all 0.18s ease;
        }}
        .hero-nav-btn:hover {{
            background: #b71c1c;
            transform: translateY(-50%) scale(1.08);
        }}
        .hero-prev {{ left: 10px; }}
        .hero-next {{ right: 10px; }}
        .hero-dots-bar {{
            position: absolute;
            bottom: 8px;
            left: 50%;
            transform: translateX(-50%);
            z-index: 8;
            display: flex;
            gap: 8px;
            align-items: center;
            background: rgba(0, 0, 0, 0.42);
            padding: 4px 11px;
            border-radius: 999px;
        }}
        .hero-dot {{
            width: 9px;
            height: 9px;
            border-radius: 999px;
            border: none;
            background: rgba(255, 255, 255, 0.6);
            cursor: pointer;
            transition: all 0.25s ease;
            padding: 0;
        }}
        .hero-dot.active {{
            width: 26px;
            background: #fde047;
            box-shadow: 0 0 8px rgba(253, 224, 71, 0.9);
        }}
        /* แถบแคปซูลวางไว้ด้านล่างนอกกรอบรูปสไลด์ (ไม่บังถ้วยไอศกรีม 100%) */
        .hero-external-capsule {{
            margin-top: 8px;
            background: linear-gradient(135deg, #b71c1c 0%, #d32f2f 50%, #991b1b 100%);
            color: #ffffff;
            border: 2px solid #fde047;
            border-radius: 999px;
            padding: 8px 16px;
            text-align: center;
            font-size: 14px;
            font-weight: 800;
            line-height: 1.35;
            box-shadow: 0 5px 14px rgba(183, 28, 28, 0.22);
        }}
        @media (max-width: 768px) {{
            #hero-carousel-root {{
                aspect-ratio: 16 / 10;
                border-radius: 16px;
                border-width: 2px;
            }}
            .hero-nav-btn {{
                width: 32px;
                height: 32px;
                font-size: 14px;
            }}
            .hero-prev {{ left: 6px; }}
            .hero-next {{ right: 6px; }}
            .hero-external-capsule {{
                font-size: 12.5px;
                padding: 7px 12px;
                border-radius: 16px;
                margin-top: 6px;
            }}
        }}
    </style>
    <div class="day-hero-wrapper">
        <div id="hero-carousel-root">
            {"".join(slides_dom_items)}
            <button type="button" class="hero-nav-btn hero-prev" aria-label="ภาพก่อนหน้า">❮</button>
            <button type="button" class="hero-nav-btn hero-next" aria-label="ภาพถัดไป">❯</button>
            <div class="hero-dots-bar">
                {"".join(dots_dom_items)}
            </div>
        </div>
        <div class="hero-external-capsule">
            🍦 3 รสชาติซิกเนเจอร์ยอดฮิต — สั่งออนไลน์เลือกคละรสได้เองจาก 30 รสชาติ ส่งฟรีทั่วไทย!
        </div>
    </div>
    <script>
        (function() {{
            var rootEl = document.getElementById('hero-carousel-root');
            if (!rootEl) return;
            var slides = rootEl.querySelectorAll('.hero-slide');
            var dots = rootEl.querySelectorAll('.hero-dot');
            var prevBtn = rootEl.querySelector('.hero-prev');
            var nextBtn = rootEl.querySelector('.hero-next');
            var totalSlides = slides.length;
            var currentSlide = 0;
            var slideInterval = null;

            function showSlide(idx) {{
                if (totalSlides === 0) return;
                currentSlide = (idx + totalSlides) % totalSlides;
                for (var i = 0; i < totalSlides; i++) {{
                    slides[i].classList.toggle('active', i === currentSlide);
                    if (dots[i]) dots[i].classList.toggle('active', i === currentSlide);
                }}
            }}

            function moveSlide(step) {{
                showSlide(currentSlide + step);
                resetTimer();
            }}

            function resetTimer() {{
                if (slideInterval) clearInterval(slideInterval);
                slideInterval = setInterval(function() {{
                    showSlide(currentSlide + 1);
                }}, 4200);
            }}

            if (prevBtn) {{
                prevBtn.addEventListener('click', function() {{ moveSlide(-1); }});
            }}
            if (nextBtn) {{
                nextBtn.addEventListener('click', function() {{ moveSlide(1); }});
            }}
            for (var d = 0; d < dots.length; d++) {{
                (function(dotIdx) {{
                    dots[dotIdx].addEventListener('click', function() {{
                        showSlide(dotIdx);
                        resetTimer();
                    }});
                }})(d);
            }}

            var touchStartX = 0;
            rootEl.addEventListener('touchstart', function(e) {{
                touchStartX = e.changedTouches[0].screenX;
            }}, {{passive: true}});
            rootEl.addEventListener('touchend', function(e) {{
                var diffX = e.changedTouches[0].screenX - touchStartX;
                if (Math.abs(diffX) > 36) {{
                    moveSlide(diffX < 0 ? 1 : -1);
                }}
            }}, {{passive: true}});

            resetTimer();
        }})();
    </script>
    """
    st.html(hero_carousel_html, unsafe_allow_javascript=True)


# ==============================================================================
# 🎨 2. ป้ายการันตี 4 ดาวทอง + ปุ่มแบนเนอร์กราฟิก Vector 3 มิติ ทั้ง 5 ปุ่ม (พร้อมป้าย 👆 คลิกที่นี่ ❯)
# ==============================================================================
def _svg_to_b64_uri(svg_raw: str) -> str:
    return "data:image/svg+xml;base64," + base64.b64encode(
        svg_raw.strip().encode("utf-8")
    ).decode("ascii")


# 1) กราฟิกหมุดแผนที่เรืองแสง (สีแดงสด-ทอง)
NAV_VEC_1_URI = _svg_to_b64_uri(
    """
<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 100 100">
  <defs>
    <radialGradient id="g1" cx="50%" cy="45%" r="52%">
      <stop offset="0%" stop-color="#fef08a"/>
      <stop offset="55%" stop-color="#f59e0b"/>
      <stop offset="100%" stop-color="#991b1b"/>
    </radialGradient>
    <linearGradient id="pin1" x1="0" y1="0" x2="1" y2="1">
      <stop offset="0%" stop-color="#ff5252"/>
      <stop offset="55%" stop-color="#dc2626"/>
      <stop offset="100%" stop-color="#7f1d1d"/>
    </linearGradient>
  </defs>
  <circle cx="50" cy="50" r="46" fill="url(#g1)" stroke="#fde047" stroke-width="3.5"/>
  <ellipse cx="50" cy="82" rx="22" ry="6.5" fill="none" stroke="#fef08a" stroke-width="2.5" stroke-dasharray="5,3"/>
  <ellipse cx="50" cy="82" rx="12" ry="3.5" fill="#fde047" opacity="0.75"/>
  <path d="M50 14 C33 14 21 26 21 42 C21 61 50 82 50 82 C50 82 79 61 79 42 C79 26 67 14 50 14 Z" fill="url(#pin1)" stroke="#fef08a" stroke-width="3"/>
  <circle cx="50" cy="41" r="15" fill="#fffbeb" stroke="#fde047" stroke-width="2.5"/>
  <path d="M44 43 L50 53 L56 43 Z" fill="#d97706"/>
  <circle cx="50" cy="38" r="7" fill="#ef4444"/>
  <circle cx="47.5" cy="35.5" r="2" fill="#ffffff"/>
</svg>
"""
)

# 2) กราฟิกถ้วยไอศกรีมพรีเมียม (สีส้ม-ชมพูสตรอว์เบอร์รี)
NAV_VEC_2_URI = _svg_to_b64_uri(
    """
<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 100 100">
  <defs>
    <radialGradient id="g2" cx="50%" cy="45%" r="52%">
      <stop offset="0%" stop-color="#fff1f2"/>
      <stop offset="55%" stop-color="#fb7185"/>
      <stop offset="100%" stop-color="#be123c"/>
    </radialGradient>
    <linearGradient id="cup2" x1="0" y1="0" x2="1" y2="1">
      <stop offset="0%" stop-color="#fde047"/>
      <stop offset="100%" stop-color="#ea580c"/>
    </linearGradient>
  </defs>
  <circle cx="50" cy="50" r="46" fill="url(#g2)" stroke="#fde047" stroke-width="3.5"/>
  <circle cx="36" cy="46" r="13" fill="#fffbeb" stroke="#fde68a" stroke-width="2"/>
  <circle cx="64" cy="46" r="13" fill="#78350f" stroke="#fcd34d" stroke-width="2"/>
  <circle cx="50" cy="38" r="15" fill="#f43f5e" stroke="#ffe4e6" stroke-width="2.5"/>
  <circle cx="50" cy="22" r="6" fill="#dc2626" stroke="#fde047" stroke-width="1.5"/>
  <path d="M23 50 L77 50 L68 81 C67 84 63 86 59 86 L41 86 C37 86 33 84 32 81 Z" fill="url(#cup2)" stroke="#ffffff" stroke-width="3"/>
  <rect x="20" y="47" width="60" height="7" rx="3.5" fill="#ffffff"/>
  <text x="50" y="73" text-anchor="middle" fill="#7f1d1d" font-size="14" font-weight="900" font-family="sans-serif">30 รส</text>
</svg>
"""
)

# 3) กราฟิกถุงทอง/ตู้ไอศกรีม (สีเขียวมรกต-ทอง)
NAV_VEC_3_URI = _svg_to_b64_uri(
    """
<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 100 100">
  <defs>
    <radialGradient id="g3" cx="50%" cy="45%" r="52%">
      <stop offset="0%" stop-color="#a7f3d0"/>
      <stop offset="55%" stop-color="#10b981"/>
      <stop offset="100%" stop-color="#064e3b"/>
    </radialGradient>
    <linearGradient id="bag3" x1="0" y1="0" x2="1" y2="1">
      <stop offset="0%" stop-color="#fef08a"/>
      <stop offset="50%" stop-color="#f59e0b"/>
      <stop offset="100%" stop-color="#b45309"/>
    </linearGradient>
  </defs>
  <circle cx="50" cy="50" r="46" fill="url(#g3)" stroke="#fde047" stroke-width="3.5"/>
  <path d="M36 22 L64 22 L57 34 L43 34 Z" fill="url(#bag3)" stroke="#ffffff" stroke-width="2"/>
  <path d="M50 32 C28 34 22 52 24 72 C25 81 35 86 50 86 C65 86 75 81 76 72 C78 52 72 34 50 32 Z" fill="url(#bag3)" stroke="#ffffff" stroke-width="2.5"/>
  <rect x="38" y="31" width="24" height="5" rx="2.5" fill="#dc2626" stroke="#fde047" stroke-width="1.5"/>
  <text x="50" y="62" text-anchor="middle" fill="#7f1d1d" font-size="18" font-weight="900" font-family="sans-serif">100%</text>
  <text x="50" y="77" text-anchor="middle" fill="#ffffff" font-size="11" font-weight="900" font-family="sans-serif">PROFIT</text>
</svg>
"""
)

# 4) กราฟิกพลุปาร์ตี้จัดเลี้ยง (สีม่วงพาสเทล-ทอง)
NAV_VEC_4_URI = _svg_to_b64_uri(
    """
<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 100 100">
  <defs>
    <radialGradient id="g4" cx="50%" cy="45%" r="52%">
      <stop offset="0%" stop-color="#f3e8ff"/>
      <stop offset="55%" stop-color="#9333ea"/>
      <stop offset="100%" stop-color="#4c1d95"/>
    </radialGradient>
    <linearGradient id="cone4" x1="0" y1="0" x2="1" y2="1">
      <stop offset="0%" stop-color="#fde047"/>
      <stop offset="100%" stop-color="#d97706"/>
    </linearGradient>
  </defs>
  <circle cx="50" cy="50" r="46" fill="url(#g4)" stroke="#fde047" stroke-width="3.5"/>
  <polygon points="22,78 44,36 64,56" fill="url(#cone4)" stroke="#ffffff" stroke-width="2.5"/>
  <circle cx="62" cy="30" r="6" fill="#f43f5e" stroke="#ffffff" stroke-width="1.5"/>
  <circle cx="75" cy="44" r="5" fill="#fde047" stroke="#ffffff" stroke-width="1.5"/>
  <circle cx="48" cy="22" r="4.5" fill="#38bdf8" stroke="#ffffff" stroke-width="1.5"/>
  <path d="M55 42 Q70 22 82 28" fill="none" stroke="#fde047" stroke-width="3.5" stroke-linecap="round"/>
  <path d="M60 50 Q76 46 84 58" fill="none" stroke="#f472b6" stroke-width="3.5" stroke-linecap="round"/>
  <polygon points="32,22 34,28 40,28 35,32 37,38 32,34 27,38 29,32 24,28 30,28" fill="#fde047"/>
</svg>
"""
)

# 5) กราฟิกมงกุฎมิชลิน & YouTube (สีน้ำเงินเข้ม-ทองมิชลิน)
NAV_VEC_5_URI = _svg_to_b64_uri(
    """
<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 100 100">
  <defs>
    <radialGradient id="g5" cx="50%" cy="45%" r="52%">
      <stop offset="0%" stop-color="#3b82f6"/>
      <stop offset="55%" stop-color="#1e3a8a"/>
      <stop offset="100%" stop-color="#0f172a"/>
    </radialGradient>
    <linearGradient id="cr5" x1="0" y1="0" x2="1" y2="1">
      <stop offset="0%" stop-color="#fef08a"/>
      <stop offset="55%" stop-color="#f59e0b"/>
      <stop offset="100%" stop-color="#b45309"/>
    </linearGradient>
  </defs>
  <circle cx="50" cy="50" r="46" fill="url(#g5)" stroke="#fde047" stroke-width="3.5"/>
  <path d="M20 52 L28 26 L43 40 L50 20 L57 40 L72 26 L80 52 Z" fill="url(#cr5)" stroke="#ffffff" stroke-width="2"/>
  <rect x="22" y="53" width="56" height="7" rx="3" fill="#fde047" stroke="#ffffff" stroke-width="1.5"/>
  <rect x="26" y="63" width="48" height="22" rx="7" fill="#dc2626" stroke="#fde047" stroke-width="2"/>
  <polygon points="45,68 45,80 58,74" fill="#ffffff"/>
</svg>
"""
)

render_html(
    f"""
<style>
    /* สไตล์ร่วมสำหรับปุ่มแบนเนอร์กราฟิก Vector 3 มิติ ทั้ง 5 ปุ่ม */
    .st-key-nav_btn_branches div.stButton > button,
    .st-key-nav_btn_order_home div.stButton > button,
    .st-key-nav_btn_franchise div.stButton > button,
    .st-key-nav_btn_catering div.stButton > button,
    .st-key-nav_btn_michelin_studio div.stButton > button {{
        display: flex !important;
        align-items: center !important;
        justify-content: space-between !important;
        gap: 14px !important;
        width: 100% !important;
        min-height: 78px !important;
        padding: 12px 16px !important;
        border-radius: 18px !important;
        text-align: left !important;
        position: relative !important;
        margin-bottom: 4px !important;
        transition: all 0.2s ease !important;
    }}
    .st-key-nav_btn_branches div.stButton > button:hover,
    .st-key-nav_btn_order_home div.stButton > button:hover,
    .st-key-nav_btn_franchise div.stButton > button:hover,
    .st-key-nav_btn_catering div.stButton > button:hover,
    .st-key-nav_btn_michelin_studio div.stButton > button:hover {{
        transform: translateY(-2px) !important;
        filter: brightness(1.06) !important;
    }}
    .st-key-nav_btn_branches div.stButton > button:active,
    .st-key-nav_btn_order_home div.stButton > button:active,
    .st-key-nav_btn_franchise div.stButton > button:active,
    .st-key-nav_btn_catering div.stButton > button:active,
    .st-key-nav_btn_michelin_studio div.stButton > button:active {{
        transform: translateY(2px) !important;
    }}

    /* ไอคอนกราฟิก Vector ด้านซ้ายมือของแต่ละปุ่ม (::before) */
    .st-key-nav_btn_branches div.stButton > button::before,
    .st-key-nav_btn_order_home div.stButton > button::before,
    .st-key-nav_btn_franchise div.stButton > button::before,
    .st-key-nav_btn_catering div.stButton > button::before,
    .st-key-nav_btn_michelin_studio div.stButton > button::before {{
        content: "" !important;
        display: block !important;
        width: 56px !important;
        height: 56px !important;
        flex-shrink: 0 !important;
        background-size: contain !important;
        background-repeat: no-repeat !important;
        background-position: center !important;
        filter: drop-shadow(0 4px 8px rgba(0, 0, 0, 0.35)) !important;
    }}
    .st-key-nav_btn_branches div.stButton > button::before {{
        background-image: url("{NAV_VEC_1_URI}") !important;
    }}
    .st-key-nav_btn_order_home div.stButton > button::before {{
        background-image: url("{NAV_VEC_2_URI}") !important;
    }}
    .st-key-nav_btn_franchise div.stButton > button::before {{
        background-image: url("{NAV_VEC_3_URI}") !important;
    }}
    .st-key-nav_btn_catering div.stButton > button::before {{
        background-image: url("{NAV_VEC_4_URI}") !important;
    }}
    .st-key-nav_btn_michelin_studio div.stButton > button::before {{
        background-image: url("{NAV_VEC_5_URI}") !important;
    }}

    /* จัดข้อความ 2 บรรทัดตรงกลางให้ชิดซ้าย ตัวหนังสือใหญ่ คมกริบ ไร้เงาเบลอ อ่านง่ายสบายตา */
    .st-key-nav_btn_branches div.stButton > button div[data-testid="stMarkdownContainer"],
    .st-key-nav_btn_order_home div.stButton > button div[data-testid="stMarkdownContainer"],
    .st-key-nav_btn_franchise div.stButton > button div[data-testid="stMarkdownContainer"],
    .st-key-nav_btn_catering div.stButton > button div[data-testid="stMarkdownContainer"],
    .st-key-nav_btn_michelin_studio div.stButton > button div[data-testid="stMarkdownContainer"] {{
        flex: 1 !important;
        text-align: left !important;
    }}
    .st-key-nav_btn_branches div.stButton > button p,
    .st-key-nav_btn_order_home div.stButton > button p,
    .st-key-nav_btn_franchise div.stButton > button p,
    .st-key-nav_btn_catering div.stButton > button p,
    .st-key-nav_btn_michelin_studio div.stButton > button p,
    .st-key-nav_btn_branches div.stButton > button[kind="secondary"] p,
    .st-key-nav_btn_order_home div.stButton > button[kind="secondary"] p,
    .st-key-nav_btn_franchise div.stButton > button[kind="secondary"] p,
    .st-key-nav_btn_catering div.stButton > button[kind="secondary"] p,
    .st-key-nav_btn_michelin_studio div.stButton > button[kind="secondary"] p,
    .st-key-nav_btn_branches div.stButton > button[kind="primary"] p,
    .st-key-nav_btn_order_home div.stButton > button[kind="primary"] p,
    .st-key-nav_btn_franchise div.stButton > button[kind="primary"] p,
    .st-key-nav_btn_catering div.stButton > button[kind="primary"] p,
    .st-key-nav_btn_michelin_studio div.stButton > button[kind="primary"] p {{
        margin: 0 !important;
        text-align: left !important;
        font-family: 'Kanit', 'Prompt', sans-serif !important;
        font-size: 14.5px !important;
        font-weight: 700 !important;
        color: #fef9c3 !important;
        line-height: 1.42 !important;
        text-shadow: none !important;
        -webkit-font-smoothing: antialiased !important;
    }}
    .st-key-nav_btn_branches div.stButton > button p strong,
    .st-key-nav_btn_order_home div.stButton > button p strong,
    .st-key-nav_btn_franchise div.stButton > button p strong,
    .st-key-nav_btn_catering div.stButton > button p strong,
    .st-key-nav_btn_michelin_studio div.stButton > button p strong {{
        display: block !important;
        font-family: 'Kanit', 'Prompt', sans-serif !important;
        font-size: 19px !important;
        font-weight: 800 !important;
        color: #ffffff !important;
        line-height: 1.28 !important;
        margin-bottom: 3px !important;
        text-shadow: none !important;
        letter-spacing: 0.15px !important;
    }}

    /* ป้ายกระตุ้นให้คลิกด้านขวามือ (::after -> 👆 คลิกที่นี่ ❯ และเปลี่ยนเป็น ✅ กำลังแสดงหน้านี้ เมื่อถูกเลือก) */
    .st-key-nav_btn_branches div.stButton > button::after,
    .st-key-nav_btn_order_home div.stButton > button::after,
    .st-key-nav_btn_franchise div.stButton > button::after,
    .st-key-nav_btn_catering div.stButton > button::after,
    .st-key-nav_btn_michelin_studio div.stButton > button::after {{
        content: "👆 คลิกที่นี่ ❯" !important;
        background: linear-gradient(135deg, #fef08a 0%, #f59e0b 100%) !important;
        color: #7f1d1d !important;
        font-size: 13px !important;
        font-weight: 900 !important;
        padding: 7px 14px !important;
        border-radius: 999px !important;
        border: 2px solid #ffffff !important;
        box-shadow: none !important;
        text-shadow: none !important;
        white-space: nowrap !important;
        flex-shrink: 0 !important;
    }}
    .st-key-nav_btn_branches div.stButton > button[kind="primary"]::after,
    .st-key-nav_btn_order_home div.stButton > button[kind="primary"]::after,
    .st-key-nav_btn_franchise div.stButton > button[kind="primary"]::after,
    .st-key-nav_btn_catering div.stButton > button[kind="primary"]::after,
    .st-key-nav_btn_michelin_studio div.stButton > button[kind="primary"]::after {{
        content: "✅ กำลังแสดงหน้านี้" !important;
        background: linear-gradient(135deg, #FFD700 0%, #fef08a 50%, #facc15 100%) !important;
        color: #7f1d1d !important;
        border: 2.5px solid #ffffff !important;
        box-shadow: 0 0 12px rgba(255, 215, 0, 0.85) !important;
    }}

    /* 1) ปุ่มที่ 1: สีแดงเข้มซิกเนเจอร์ตัดตัวหนังสือขาวคมชัด (ล็อกสีพื้นหลังทุกสถานะ ห้ามขาวโพลนเด็ดขาด!) */
    .st-key-nav_btn_branches div.stButton > button,
    .st-key-nav_btn_branches div.stButton > button:hover,
    .st-key-nav_btn_branches div.stButton > button:focus,
    .st-key-nav_btn_branches div.stButton > button:active,
    .st-key-nav_btn_branches div.stButton > button:focus-visible,
    .st-key-nav_btn_branches div.stButton > button[kind="primary"],
    .st-key-nav_btn_branches div.stButton > button[kind="secondary"],
    .st-key-nav_btn_branches div.stButton > button[kind="primary"]:hover,
    .st-key-nav_btn_branches div.stButton > button[kind="primary"]:focus,
    .st-key-nav_btn_branches div.stButton > button[kind="primary"]:active,
    .st-key-nav_btn_branches div.stButton > button[kind="secondary"]:hover,
    .st-key-nav_btn_branches div.stButton > button[kind="secondary"]:focus,
    .st-key-nav_btn_branches div.stButton > button[kind="secondary"]:active {{
        background: linear-gradient(135deg, #991b1b 0%, #b91c1c 55%, #dc2626 100%) !important;
        background-color: #b91c1c !important;
        color: #ffffff !important;
        border: 2.5px solid #fde047 !important;
        box-shadow: 0 4px 0 #7f1d1d, 0 8px 18px rgba(185, 28, 28, 0.25) !important;
    }}
    /* 2) ปุ่มที่ 2: สีแดงเชอร์รี่-ชมพูเข้มตัดตัวหนังสือขาวคมชัด */
    .st-key-nav_btn_order_home div.stButton > button,
    .st-key-nav_btn_order_home div.stButton > button:hover,
    .st-key-nav_btn_order_home div.stButton > button:focus,
    .st-key-nav_btn_order_home div.stButton > button:active,
    .st-key-nav_btn_order_home div.stButton > button:focus-visible,
    .st-key-nav_btn_order_home div.stButton > button[kind="primary"],
    .st-key-nav_btn_order_home div.stButton > button[kind="secondary"],
    .st-key-nav_btn_order_home div.stButton > button[kind="primary"]:hover,
    .st-key-nav_btn_order_home div.stButton > button[kind="primary"]:focus,
    .st-key-nav_btn_order_home div.stButton > button[kind="primary"]:active,
    .st-key-nav_btn_order_home div.stButton > button[kind="secondary"]:hover,
    .st-key-nav_btn_order_home div.stButton > button[kind="secondary"]:focus,
    .st-key-nav_btn_order_home div.stButton > button[kind="secondary"]:active {{
        background: linear-gradient(135deg, #9f1239 0%, #be123c 55%, #e11d48 100%) !important;
        background-color: #be123c !important;
        color: #ffffff !important;
        border: 2.5px solid #fde047 !important;
        box-shadow: 0 4px 0 #881337, 0 8px 18px rgba(190, 18, 60, 0.25) !important;
    }}
    /* 3) ปุ่มที่ 3: สีเขียวมรกตเข้มตัดตัวหนังสือขาวคมชัด */
    .st-key-nav_btn_franchise div.stButton > button,
    .st-key-nav_btn_franchise div.stButton > button:hover,
    .st-key-nav_btn_franchise div.stButton > button:focus,
    .st-key-nav_btn_franchise div.stButton > button:active,
    .st-key-nav_btn_franchise div.stButton > button:focus-visible,
    .st-key-nav_btn_franchise div.stButton > button[kind="primary"],
    .st-key-nav_btn_franchise div.stButton > button[kind="secondary"],
    .st-key-nav_btn_franchise div.stButton > button[kind="primary"]:hover,
    .st-key-nav_btn_franchise div.stButton > button[kind="primary"]:focus,
    .st-key-nav_btn_franchise div.stButton > button[kind="primary"]:active,
    .st-key-nav_btn_franchise div.stButton > button[kind="secondary"]:hover,
    .st-key-nav_btn_franchise div.stButton > button[kind="secondary"]:focus,
    .st-key-nav_btn_franchise div.stButton > button[kind="secondary"]:active {{
        background: linear-gradient(135deg, #064e3b 0%, #047857 55%, #059669 100%) !important;
        background-color: #047857 !important;
        color: #ffffff !important;
        border: 2.5px solid #fde047 !important;
        box-shadow: 0 4px 0 #022c22, 0 8px 18px rgba(4, 120, 87, 0.25) !important;
    }}
    /* 4) ปุ่มที่ 4: สีม่วงเข้มตัดตัวหนังสือขาวคมชัด */
    .st-key-nav_btn_catering div.stButton > button,
    .st-key-nav_btn_catering div.stButton > button:hover,
    .st-key-nav_btn_catering div.stButton > button:focus,
    .st-key-nav_btn_catering div.stButton > button:active,
    .st-key-nav_btn_catering div.stButton > button:focus-visible,
    .st-key-nav_btn_catering div.stButton > button[kind="primary"],
    .st-key-nav_btn_catering div.stButton > button[kind="secondary"],
    .st-key-nav_btn_catering div.stButton > button[kind="primary"]:hover,
    .st-key-nav_btn_catering div.stButton > button[kind="primary"]:focus,
    .st-key-nav_btn_catering div.stButton > button[kind="primary"]:active,
    .st-key-nav_btn_catering div.stButton > button[kind="secondary"]:hover,
    .st-key-nav_btn_catering div.stButton > button[kind="secondary"]:focus,
    .st-key-nav_btn_catering div.stButton > button[kind="secondary"]:active {{
        background: linear-gradient(135deg, #4c1d95 0%, #6d28d9 55%, #7c3aed 100%) !important;
        background-color: #6d28d9 !important;
        color: #ffffff !important;
        border: 2.5px solid #fde047 !important;
        box-shadow: 0 4px 0 #3b0764, 0 8px 18px rgba(109, 40, 217, 0.25) !important;
    }}
    /* 5) ปุ่มที่ 5: สีน้ำเงินกรมท่ามิชลินตัดตัวหนังสือขาวคมชัด */
    .st-key-nav_btn_michelin_studio div.stButton > button,
    .st-key-nav_btn_michelin_studio div.stButton > button:hover,
    .st-key-nav_btn_michelin_studio div.stButton > button:focus,
    .st-key-nav_btn_michelin_studio div.stButton > button:active,
    .st-key-nav_btn_michelin_studio div.stButton > button:focus-visible,
    .st-key-nav_btn_michelin_studio div.stButton > button[kind="primary"],
    .st-key-nav_btn_michelin_studio div.stButton > button[kind="secondary"],
    .st-key-nav_btn_michelin_studio div.stButton > button[kind="primary"]:hover,
    .st-key-nav_btn_michelin_studio div.stButton > button[kind="primary"]:focus,
    .st-key-nav_btn_michelin_studio div.stButton > button[kind="primary"]:active,
    .st-key-nav_btn_michelin_studio div.stButton > button[kind="secondary"]:hover,
    .st-key-nav_btn_michelin_studio div.stButton > button[kind="secondary"]:focus,
    .st-key-nav_btn_michelin_studio div.stButton > button[kind="secondary"]:active {{
        background: linear-gradient(135deg, #0f172a 0%, #1e3a8a 55%, #1d4ed8 100%) !important;
        background-color: #1e3a8a !important;
        color: #ffffff !important;
        border: 2.5px solid #fde047 !important;
        box-shadow: 0 4px 0 #020617, 0 8px 18px rgba(30, 58, 138, 0.28) !important;
    }}

    /* ไฮไลต์ขอบสีทองเรืองแสงหนา 4px solid #FFD700 สำหรับปุ่มหน้าที่กำลังเปิดอยู่ (kind="primary") */
    .st-key-nav_btn_branches div.stButton > button[kind="primary"],
    .st-key-nav_btn_order_home div.stButton > button[kind="primary"],
    .st-key-nav_btn_franchise div.stButton > button[kind="primary"],
    .st-key-nav_btn_catering div.stButton > button[kind="primary"],
    .st-key-nav_btn_michelin_studio div.stButton > button[kind="primary"],
    .st-key-nav_btn_branches div.stButton > button[kind="primary"]:hover,
    .st-key-nav_btn_order_home div.stButton > button[kind="primary"]:hover,
    .st-key-nav_btn_franchise div.stButton > button[kind="primary"]:hover,
    .st-key-nav_btn_catering div.stButton > button[kind="primary"]:hover,
    .st-key-nav_btn_michelin_studio div.stButton > button[kind="primary"]:hover,
    .st-key-nav_btn_branches div.stButton > button[kind="primary"]:focus,
    .st-key-nav_btn_order_home div.stButton > button[kind="primary"]:focus,
    .st-key-nav_btn_franchise div.stButton > button[kind="primary"]:focus,
    .st-key-nav_btn_catering div.stButton > button[kind="primary"]:focus,
    .st-key-nav_btn_michelin_studio div.stButton > button[kind="primary"]:focus,
    .st-key-nav_btn_branches div.stButton > button[kind="primary"]:active,
    .st-key-nav_btn_order_home div.stButton > button[kind="primary"]:active,
    .st-key-nav_btn_franchise div.stButton > button[kind="primary"]:active,
    .st-key-nav_btn_catering div.stButton > button[kind="primary"]:active,
    .st-key-nav_btn_michelin_studio div.stButton > button[kind="primary"]:active {{
        border: 4px solid #FFD700 !important;
        outline: 2px solid #ffffff !important;
        box-shadow: 0 0 20px rgba(255, 215, 0, 0.75), 0 6px 20px rgba(0, 0, 0, 0.35) !important;
    }}

    @media (max-width: 768px) {{
        .st-key-nav_btn_branches div.stButton > button,
        .st-key-nav_btn_order_home div.stButton > button,
        .st-key-nav_btn_franchise div.stButton > button,
        .st-key-nav_btn_catering div.stButton > button,
        .st-key-nav_btn_michelin_studio div.stButton > button {{
            min-height: 76px !important;
            padding: 11px 12px !important;
            gap: 10px !important;
            border-radius: 16px !important;
        }}
        .st-key-nav_btn_branches div.stButton > button::before,
        .st-key-nav_btn_order_home div.stButton > button::before,
        .st-key-nav_btn_franchise div.stButton > button::before,
        .st-key-nav_btn_catering div.stButton > button::before,
        .st-key-nav_btn_michelin_studio div.stButton > button::before {{
            width: 48px !important;
            height: 48px !important;
            filter: none !important;
        }}
        .st-key-nav_btn_branches div.stButton > button p strong,
        .st-key-nav_btn_order_home div.stButton > button p strong,
        .st-key-nav_btn_franchise div.stButton > button p strong,
        .st-key-nav_btn_catering div.stButton > button p strong,
        .st-key-nav_btn_michelin_studio div.stButton > button p strong {{
            font-size: 16px !important;
            line-height: 1.28 !important;
            text-shadow: none !important;
        }}
        .st-key-nav_btn_branches div.stButton > button p,
        .st-key-nav_btn_order_home div.stButton > button p,
        .st-key-nav_btn_franchise div.stButton > button p,
        .st-key-nav_btn_catering div.stButton > button p,
        .st-key-nav_btn_michelin_studio div.stButton > button p {{
            font-size: 12.8px !important;
            line-height: 1.35 !important;
            text-shadow: none !important;
        }}
        .st-key-nav_btn_branches div.stButton > button::after,
        .st-key-nav_btn_order_home div.stButton > button::after,
        .st-key-nav_btn_franchise div.stButton > button::after,
        .st-key-nav_btn_catering div.stButton > button::after,
        .st-key-nav_btn_michelin_studio div.stButton > button::after {{
            content: "👆 คลิก ❯" !important;
            font-size: 11.5px !important;
            padding: 5px 10px !important;
        }}
        .st-key-nav_btn_branches div.stButton > button[kind="primary"]::after,
        .st-key-nav_btn_order_home div.stButton > button[kind="primary"]::after,
        .st-key-nav_btn_franchise div.stButton > button[kind="primary"]::after,
        .st-key-nav_btn_catering div.stButton > button[kind="primary"]::after,
        .st-key-nav_btn_michelin_studio div.stButton > button[kind="primary"]::after {{
            content: "✅ กำลังแสดงหน้านี้" !important;
            font-size: 11px !important;
            padding: 5px 9px !important;
        }}
    }}
</style>
<div class="swensens-badges-grid" style="margin:6px 0 10px 0;">
<span class="swensens-gold-badge">⭐ มาตรฐานร้าน Michelin Guide 10+ สาขา</span>
<span class="swensens-gold-badge">⭐ ร้านอาหารชั้นนำทั่วประเทศ 200 สาขา</span>
<span class="swensens-gold-badge">⭐ เปิดแล้วกำไร 100% ไม่มีทางขาดทุน</span>
<span class="swensens-gold-badge">⭐ คืนค่าแฟรนไชส์ 100% เจ้าเดียวในไทย!</span>
</div>
"""
)

if "active_page" not in st.session_state:
    st.session_state["active_page"] = "branches"

flavors_list = flavors_cfg.get("flavors", [])
available_flavors_count = sum(1 for f in flavors_list if not f.get("out_of_stock"))
oos_flavors_count = sum(1 for f in flavors_list if f.get("out_of_stock"))

core = links_cfg.get("core_links", DEFAULT_LINKS_CONFIG["core_links"])
promo_item = core.get("order_promo", DEFAULT_LINKS_CONFIG["core_links"]["order_promo"])
line_item = core.get("franchise_line", DEFAULT_LINKS_CONFIG["core_links"]["franchise_line"])
web_item = core.get("website", DEFAULT_LINKS_CONFIG["core_links"]["website"])
fb_item = core.get("facebook", DEFAULT_LINKS_CONFIG["core_links"]["facebook"])
tiktok_item = core.get("tiktok", DEFAULT_LINKS_CONFIG["core_links"]["tiktok"])
yt_item = core.get("youtube", DEFAULT_LINKS_CONFIG["core_links"]["youtube"])

current_page = st.session_state.get("active_page", "branches")

# 📲 จุดที่ 1: แถบและปุ่มติดตั้งแอป Day Ice Cream ลงมือถือ (เหนือหัวข้อ 👆 เลือกเมนูบริการของ เดย์ไอศกรีม)
render_pwa_install_banner("top_nav", PWA_ASSETS)

with st.container(border=True):
    render_html(
        '<div style="text-align:center;background:linear-gradient(90deg,#fff1f2,#fffbeb,#fff1f2);border:1.5px dashed #ef4444;border-radius:12px;padding:6px 12px;margin-bottom:8px;font-size:13.5px;font-weight:800;color:#b91c1c;">👆 เลือกเมนูบริการของ เดย์ไอศกรีม (จิ้มที่ปุ่มด้านล่างได้เลยครับ ❯)</div>'
    )

    # 1) ปุ่มที่ 1 (สีแดงสด-ทอง): กราฟิกหมุดแผนที่เรืองแสง
    if st.button(
        "**📍 1. ค้นหา 300+ สาขาใกล้บ้านคุณ**  \n👉 กดค้นหาพิกัดร้านใกล้คุณ & นำทาง GPS คลิกที่นี่ ❯",
        key="nav_btn_branches",
        type="primary" if current_page == "branches" else "secondary",
        use_container_width=True,
    ):
        st.session_state["active_page"] = "branches"
        st.session_state["gps_active"] = True
        st.session_state["gps_req_id"] = int(st.session_state.get("gps_req_id", 0)) + 1
        st.rerun()

    # 2) ปุ่มที่ 2 (สีส้ม-ชมพูสตรอว์เบอร์รี): กราฟิกถ้วยไอศกรีมพรีเมียม
    if st.button(
        "**🍨 2. สั่งไอศกรีมส่งถึงบ้าน (เลือกได้ 30 รส)**  \n👉 โปร 22 ถ้วย 990.- ส่งฟรีทั่วไทย! จิ้มเลือกรสชาติที่นี่ ❯",
        key="nav_btn_order_home",
        type="primary" if current_page == "order_home" else "secondary",
        use_container_width=True,
    ):
        st.session_state["active_page"] = "order_home"
        st.rerun()

    # 3) ปุ่มที่ 3 (สีเขียวมรกต-ทอง): กราฟิกถุงทอง/ตู้ไอศกรีม
    if st.button(
        "**💰 3. สมัครแฟรนไชส์กำไร 100% (คืนมัดจำ 100%)**  \n👉 ทดลองกดเครื่องคิดเลขคำนวณกำไรต่อปี คลิกที่นี่ ❯",
        key="nav_btn_franchise",
        type="primary" if current_page == "franchise" else "secondary",
        use_container_width=True,
    ):
        st.session_state["active_page"] = "franchise"
        st.rerun()

    # 4) ปุ่มที่ 4 (สีม่วงพาสเทล-ทอง): กราฟิกพลุปาร์ตี้จัดเลี้ยง
    if st.button(
        "**🎉 4. จองไอศกรีมจัดเลี้ยงนอกสถานที่**  \n👉 สำหรับงานบุญ งานแต่ง อีเวนต์ (150-200+ ถ้วย) คลิกที่นี่ ❯",
        key="nav_btn_catering",
        type="primary" if current_page == "catering" else "secondary",
        use_container_width=True,
    ):
        st.session_state["active_page"] = "catering"
        st.rerun()

    # 5) ปุ่มที่ 5 (สีน้ำเงินเข้ม-ทองมิชลิน): กราฟิกมงกุฎมิชลิน & YouTube
    if st.button(
        "**🏆 5. มาตรฐาน Michelin Guide & ช่อง DAY STUDIO**  \n👉 ดูรีวิวความภูมิใจ ยอดวิว 323,499+ ครั้ง คลิกที่นี่ ❯",
        key="nav_btn_michelin_studio",
        type="primary" if current_page == "michelin_studio" else "secondary",
        use_container_width=True,
    ):
        st.session_state["active_page"] = "michelin_studio"
        st.rerun()


# ==============================================================================
# ฟังก์ชันแสดงโซน "🎬 วิดีโอไวรัล & พรีเซนเทชันปิดการขายครบวงจร" (Storytelling Funnel)
# 1) วิดีโอที่ 1 (ข่าวด่วน! ทั่วโลกตะลึง! ไอติมไทย) + TikTok Embed @dayicecream
# 2) ชุดภาพโฆษณาหลัก 4 ภาพ (+ ภาพที่ 5 & 6) เรียงตามลำดับการเล่าเรื่อง
# 3) วิดีโอที่ 2 ("ไอศกรีมที่จริงใจที่สุด") + Facebook Page Dayicecream
# ==============================================================================
def render_clean_michelin_gallery(
    key_prefix: str = "main", show_top_cta: bool = True
) -> None:
    if show_top_cta:
        render_html(
            f"""
<div class="cta-grid" style="margin-top:8px;">
<a class="cta-card cta-line" href="{line_item.get('url')}" target="_blank" rel="noopener noreferrer">
<div style="width:48px;height:48px;border-radius:14px;background:#ffffff;color:#059669;display:flex;align-items:center;justify-content:center;font-size:26px;flex-shrink:0;">💬</div>
<div>
<div class="cta-title">💬 สมัครแฟรนไชส์ ฟรี / สั่งซื้อผ่าน LINE: Dayinterfood</div>
<div class="cta-url">👉 แอดไลน์พูดคุยกับคุณเดย์โดยตรง คลิกที่นี่</div>
</div>
</a>
<a class="cta-card cta-web" href="{web_item.get('url')}" target="_blank" rel="noopener noreferrer">
<div style="width:48px;height:48px;border-radius:14px;background:#ffffff;color:#ea580c;display:flex;align-items:center;justify-content:center;font-size:26px;flex-shrink:0;">🌐</div>
<div>
<div class="cta-title">🌐 เว็บไซต์หลัก www.dayicecream.com & แอป app.dayicecream.com</div>
<div class="cta-url">👉 ดูรายละเอียดผลิตภัณฑ์ แฟรนไชส์ และสั่งซื้อผ่านเว็บแอป</div>
</div>
</a>
</div>
<div class="social-row" style="margin-bottom:14px;">
<a class="social-pill" href="{fb_item.get('url')}" target="_blank" rel="noopener noreferrer">
<span>📘 <b>Facebook:</b> ติดตามข่าวสาร แฟรนไชส์เปิดใหม่</span>
<span style="color:#d32f2f;font-size:12.5px;">เปิดเพจ ↗</span>
</a>
<a class="social-pill" href="{tiktok_item.get('url')}" target="_blank" rel="noopener noreferrer">
<span>🎵 <b>TikTok:</b> @dayicecream (ผู้ติดตาม 120K+ • ยอดวิว 12 ล้านวิว!)</span>
<span style="color:#d32f2f;font-size:12.5px;">ดูคลิป ↗</span>
</a>
<a class="social-pill" href="{yt_item.get('url')}" target="_blank" rel="noopener noreferrer">
<span>▶️ <b>YouTube:</b> Day Ice Cream Official</span>
<span style="color:#d32f2f;font-size:12.5px;">รับชม ↗</span>
</a>
</div>
"""
        )

    v1_cfg = viral_videos_cfg.get("video_1", {})
    v2_cfg = viral_videos_cfg.get("video_2", {})

    v1_title = v1_cfg.get(
        "title",
        '🔴 วิดีโอไวรัลทะลุล้านวิว: "ข่าวด่วน! ทั่วโลกตะลึง! ไอติมไทย สูตรลับ ไม่พึ่งเคมี แต่อร่อยจนต้องร้องขอชีวิต!"',
    )
    v1_sub = v1_cfg.get(
        "subtitle",
        "ต่างชาติยังทึ่ง! ไอศกรีมเมืองไทยเจ้านี้ ไม่ใส่สารขึ้นรูป ไม่พึ่งเคมี แล้วทำไอศกรีมให้อร่อยระดับมิชลินได้ยังไง? • ยอดวิวทะลุล้านวิวบน TikTok @dayicecream",
    )
    v1_ext_url = (
        v1_cfg.get("external_url", "https://www.tiktok.com/@dayicecream").strip()
        or "https://www.tiktok.com/@dayicecream"
    )
    v1_ext_label = v1_cfg.get(
        "external_btn_label",
        "🎵 กดรับชมคลิปเต็มและติดตามบน TikTok @dayicecream (ผู้ติดตาม 120K+ • ยอดวิว 12.18 ล้านวิว!) ↗",
    )
    v1_playable = resolve_playable_video_path(v1_cfg.get("video_path", ""), slot_num=1)

    v2_title = v2_cfg.get(
        "title",
        '🍦 วิดีโอพิเศษ: "ไอศกรีมที่จริงใจที่สุด" — เบื้องหลังความตั้งใจของทีมงาน เดย์ ไอศกรีม ส่งความสุขให้คุณทุกวัน',
    )
    v2_sub = v2_cfg.get(
        "subtitle",
        "เบื้องหลังความตั้งใจของทีมงานและโรงงาน เดย์ ไอศกรีม คัดสรรวัตถุดิบธรรมชาติแท้ 100% ไร้สารเคมี เพื่อส่งความสุขให้คุณทุกวัน",
    )
    v2_ext_url = (
        v2_cfg.get("external_url", "https://www.facebook.com/dayicecream").strip()
        or "https://www.facebook.com/dayicecream"
    )
    v2_ext_label = v2_cfg.get(
        "external_btn_label",
        "📘 กดรับชมบนเพจ Facebook: Dayicecream แฟรนไชส์ไอศครีมที่ดีที่สุด ↗",
    )
    v2_playable = resolve_playable_video_path(v2_cfg.get("video_path", ""), slot_num=2)

    # --------------------------------------------------------------------------
    # STEP 0: แบนเนอร์เปิดโซน Storytelling Funnel
    # --------------------------------------------------------------------------
    render_html(
        """
<div style="background:linear-gradient(135deg,#fffDF9 0%,#fff1f2 100%);border:2.5px solid #fca5a5;border-radius:22px;padding:18px 16px;text-align:center;margin-bottom:16px;box-shadow:0 8px 24px rgba(211,47,47,0.09);">
<span style="background:linear-gradient(135deg,#d32f2f,#ff5252);color:#ffffff;font-weight:800;font-size:12.5px;padding:5px 15px;border-radius:99px;display:inline-block;">🎬 วิดีโอไวรัล & พรีเซนเทชันปิดการขายครบวงจร (STORYTELLING FUNNEL)</span>
<h2 style="font-family:'Kanit','Prompt',sans-serif;color:#b71c1c;font-size:22px;font-weight:800;margin:10px 0 10px 0;line-height:1.35;">👑 ทำไมร้านอาหารระดับ Michelin Guide กว่า 10 สาขา และลูกค้ากว่า 323,499 คน ถึงเลือก เดย์ ไอศกรีม?</h2>
<div style="display:inline-flex;align-items:center;gap:8px;background:linear-gradient(135deg,#111827 0%,#b91c1c 60%,#dc2626 100%);color:#fef08a;font-weight:900;font-size:16px;padding:8px 20px;border-radius:999px;border:2px solid #fde047;box-shadow:0 6px 18px rgba(211,47,47,0.28);margin-bottom:6px;">
<span>👁️ ดู 323,499+ ครั้ง</span>
</div>
<div style="color:#5C4033;font-size:13px;font-weight:700;margin-top:4px;">รับชม 2 วิดีโอไฮไลต์และ 6 ภาพพรีเซนเทชันที่จะทำให้คุณมั่นใจ 100% ก่อนสั่งชิมหรือเปิดร้านแฟรนไชส์</div>
</div>
"""
    )

    # --------------------------------------------------------------------------
    # STEP 1: 🎥 วิดีโอที่ 1 (เปิดหัวสร้างความตะลึง) + TikTok @dayicecream
    # --------------------------------------------------------------------------
    with st.container(border=True):
        render_html(
            f"""
<div style="background:linear-gradient(135deg,#991b1b 0%,#dc2626 55%,#ef4444 100%);border:2.5px solid #fde047;border-radius:18px;padding:14px 16px;color:#ffffff;margin-bottom:12px;box-shadow:0 8px 22px rgba(211,47,47,0.24);">
<div style="display:flex;justify-content:space-between;align-items:center;flex-wrap:wrap;gap:8px;margin-bottom:6px;">
<span style="background:#fef08a;color:#991b1b;font-weight:900;font-size:12px;padding:4px 12px;border-radius:99px;">🎥 STEP 1 • วิดีโอเปิดหัวสร้างความตะลึง (VIRAL MILLION-VIEW VIDEO)</span>
<span style="background:rgba(17,24,39,0.85);color:#fef08a;font-weight:800;font-size:12px;padding:4px 12px;border-radius:99px;border:1px solid #fde047;">🔥 ยอดวิวทะลุล้านวิวบน TikTok @dayicecream</span>
</div>
<div style="font-family:'Kanit','Prompt',sans-serif;font-size:19px;font-weight:800;color:#ffffff;line-height:1.35;">{v1_title}</div>
<div style="font-size:13.5px;color:#fef2f2;margin-top:4px;line-height:1.45;">{v1_sub}</div>
</div>
"""
        )

        v1_col_video, v1_col_tiktok = st.columns([1.15, 1.0])
        with v1_col_video:
            if v1_playable and (
                v1_playable.startswith("http") or Path(v1_playable).exists()
            ):
                try:
                    st.video(v1_playable)
                except Exception:
                    st.info("กำลังเตรียมสตรีมวิดีโอข่าวด่วนไอติมไทย กรุณารอสักครู่...")
                render_html(
                    '<div style="text-align:center;color:#b71c1c;font-size:12.5px;font-weight:800;margin-top:4px;">👆 กดปุ่ม ▶️ ด้านบนเพื่อเล่นวิดีโอ "นักข่าวโลกตะลึง" พร้อมเสียงบนหน้าเว็บได้ทันที!</div>'
                )
            else:
                st.warning("กำลังค้นหาไฟล์วิดีโอ นักข่าวโลกตะลึง.mp4 ในโฟลเดอร์ vdo...")

        with v1_col_tiktok:
            render_html(
                f"""
<div style="background:linear-gradient(145deg,#111827 0%,#1f2937 60%,#374151 100%);border:2.5px solid #f43f5e;border-radius:18px;padding:16px;color:#ffffff;box-shadow:0 10px 26px rgba(0,0,0,0.22);">
<div style="display:flex;align-items:center;justify-content:space-between;flex-wrap:wrap;gap:8px;margin-bottom:10px;">
<span style="background:linear-gradient(135deg,#f43f5e,#ec4899);color:#ffffff;font-weight:800;font-size:12px;padding:4px 12px;border-radius:99px;">🎵 OFFICIAL TIKTOK CHANNEL</span>
<span style="color:#fef08a;font-size:12px;font-weight:800;">⭐ 120.2K Followers • 1.2M Likes</span>
</div>
<div style="font-family:'Kanit','Prompt',sans-serif;font-size:18px;font-weight:800;color:#ffffff;margin-bottom:6px;">🎵 TikTok: @dayicecream (เดย์ ไอศกรีม)</div>
<div style="font-size:13px;color:#e5e7eb;line-height:1.5;margin-bottom:12px;">
<b>"ข่าวด่วน! ทั่วโลกตะลึง! ไอติมไทย สูตรลับ ไม่พึ่งเคมี แต่อร่อยจนต้องร้องขอชีวิต!"</b><br>
• ต่างชาติยังทึ่ง! ไอศกรีมเมืองไทยเจ้านี้ ไม่ใส่สารขึ้นรูป ไม่ใช้อิมัลซิไฟเออร์ ไม่พึ่งเคมี<br>
• ยอดรับชมรวมทุกคลิปกว่า <b style="color:#fef08a;">12.18 ล้านวิว!</b> พิสูจน์ความอร่อยระดับร้าน Michelin Guide
</div>
<a href="{v1_ext_url}" target="_blank" rel="noopener noreferrer" style="display:block;text-align:center;background:linear-gradient(135deg,#f43f5e 0%,#e11d48 55%,#be123c 100%);color:#ffffff;font-weight:800;font-size:14.5px;padding:13px 16px;border-radius:14px;text-decoration:none;border:2px solid #fecdd3;box-shadow:0 8px 20px rgba(244,63,94,0.38);margin-bottom:8px;">{v1_ext_label}</a>
</div>
"""
            )
            with st.expander("📱 คลิกเปิดหน้าต่าง TikTok Embed (@dayicecream) บนหน้าเว็บ"):
                components.html(
                    """
<blockquote class="tiktok-embed" cite="https://www.tiktok.com/@dayicecream" data-unique-id="dayicecream" data-embed-type="creator" style="max-width: 780px; min-width: 288px;">
  <section>
    <a target="_blank" href="https://www.tiktok.com/@dayicecream?refer=creator_embed">@dayicecream</a>
  </section>
</blockquote>
<script async src="https://www.tiktok.com/embed.js"></script>
""",
                    height=430,
                    scrolling=True,
                )

    # --------------------------------------------------------------------------
    # STEP 2: 🖼️ ชุดภาพโฆษณาหลัก 4 ภาพ (+ ภาพที่ 5 & 6) เรียงต่อกันอย่างสวยงาม
    # --------------------------------------------------------------------------
    render_html(
        """
<div style="background:linear-gradient(135deg,#fffbeb 0%,#fff1f2 100%);border:2px solid #f59e0b;border-radius:18px;padding:14px 16px;margin:16px 0 12px 0;display:flex;align-items:center;justify-content:space-between;flex-wrap:wrap;gap:10px;">
<div>
<span style="background:linear-gradient(135deg,#d97706,#b45309);color:#ffffff;font-weight:800;font-size:12px;padding:4px 12px;border-radius:99px;">🖼️ STEP 2 • พรีเซนเทชันปิดการขายครบวงจร (6 ภาพหลัก)</span>
<div style="font-family:'Kanit','Prompt',sans-serif;font-size:19px;font-weight:800;color:#b71c1c;margin-top:4px;">🏆 เจาะลึกความอร่อยระดับ Michelin Guide & สิทธิประโยชน์แฟรนไชส์คืนเงินมัดจำ 100%</div>
</div>
<span style="color:#78350f;font-size:12.5px;font-weight:700;">🔍 กดปุ่มใต้ภาพเพื่อขยายดูรายละเอียดขนาดใหญ่คมชัด</span>
</div>
"""
    )

    story_poster_overrides = {
        "ป้ายโฆษณา 001.jpg": {
            "badge": "🥥 ภาพที่ 1 • วัตถุดิบธรรมชาติแท้ 100%",
            "title": "ความสุขที่คุณสัมผัสได้ (ไอศกรีมรวมมิตร กะทิทับสะแกคั้นสด & มะพร้าวน้ำหอมบ้านแพ้ว 100%)",
            "subtitle": "คัดสรรสุดยอดวัตถุดิบไทยแท้ กะทิทับสะแกคั้นสดและน้ำมะพร้าวน้ำหอมบ้านแพ้ว 100% หอมมันเข้มข้น ไม่ผสมน้ำเปล่าและไม่ใส่สารเคมี",
        },
        "ป้ายโฆษณา 002.jpg": {
            "badge": "🏆 ภาพที่ 2 • มาตรฐานระดับ Michelin Guide",
            "title": "มาตรฐานระดับโลก ที่ร้าน Michelin Guide & Bib Gourmand กว่า 10 สาขาไว้วางใจ",
            "subtitle": "การันตีคุณภาพด้วยร้านอาหารระดับมิชลินไกด์และบิบ กูร์มองด์ กว่า 10 สาขา และร้านอาหารชั้นนำทั่วประเทศกว่า 200 สาขาเลือกเสิร์ฟ",
        },
        "ป้ายโฆษณา 003.jpg": {
            "badge": "🛡️ ภาพที่ 3 • เปิดแล้วกำไร 100% คืนมัดจำ 100%",
            "title": "ประโยชน์ของการเปิดแฟรนไชส์ Day Ice Cream 6 ข้อ (เปิดแล้วกำไร 100% คืนค่ามัดจำตู้ 100%)",
            "subtitle": "ไม่ต้องซื้อแฟรนไชส์ เพียงยืมตู้แช่ประหยัดไฟ แถมฟรีไอศกรีมวันเปิดร้าน กำไรรอบแรก 5,000-10,000 บาท เลิกขายคืนเงินมัดจำ 100% ตลอดสัญญา 10 ปี",
        },
        "ป้ายโฆษณา 004.jpg": {
            "badge": "🍨 ภาพที่ 4 • เมนูโฮมเมดพรีเมียม 100% Organic",
            "title": "ป้ายเมนูไอศกรีมโฮมเมดพรีเมียม 100% Organic (ครบทุกรสชาติซิกเนเจอร์ขายดี)",
            "subtitle": "รวมรสชาติยอดนิยมจากกะทิคั้นสด นมโคสดแท้นิวซีแลนด์ และผลไม้สดแท้ตามฤดูกาล ปราศจากสารเสริมคุณภาพและสารกันบูด",
        },
        "ป้ายโฆษณา 005.jpg": {
            "badge": "🎵 ภาพที่ 5 • ฐานแฟนคลับ TikTok 120K+",
            "title": "ช่อง TikTok @dayicecream ผู้ติดตามกว่า 120.2K คน และยอดถูกใจกว่า 1.2 ล้านครั้ง!",
            "subtitle": "แบรนด์ไอศกรีมไทยที่มีฐานแฟนคลับเหนียวแน่นและเติบโตเร็วที่สุด ช่วยดึงดูดลูกค้าใหม่เข้าร้านแฟรนไชส์ทุกวัน",
        },
        "ป้ายโฆษณา 006.jpg": {
            "badge": "📈 ภาพที่ 6 • สถิติยอดวิว 12.18 ล้านวิว!",
            "title": "สถิติยอดรับชมจริงทะลุ 12.18 ล้านวิว! พลังการตลาดออนไลน์ช่วยโปรโมตร้านสาขาทั่วไทย",
            "subtitle": "เข้าถึงผู้ชมกว่า 9.57 ล้านคน สร้างการรับรู้แบรนด์ในวงกว้าง ทำให้สินค้าขายง่าย กำไรดีตั้งแต่วันแรกที่ลงตู้",
        },
    }

    gallery_items = promo_gallery_cfg.get("items", [])
    valid_gallery_items = [
        it
        for it in gallery_items
        if not str(it.get("filename", "")).lower().startswith("slide_")
        and not str(it.get("filename", "")).lower().startswith("franchise_pkg_")
        and (PROMO_GALLERY_DIR / it.get("filename", "")).exists()
    ]

    if valid_gallery_items:
        gal_cols_per_row = 2
        for g_row_start in range(0, len(valid_gallery_items), gal_cols_per_row):
            g_row_slice = valid_gallery_items[
                g_row_start : g_row_start + gal_cols_per_row
            ]
            g_cols = st.columns(gal_cols_per_row)
            for g_col_idx, g_item in enumerate(g_row_slice):
                g_num = g_row_start + g_col_idx + 1
                g_fname = g_item.get("filename", "")
                g_fpath = PROMO_GALLERY_DIR / g_fname
                ov = story_poster_overrides.get(g_fname, {})
                g_badge = ov.get("badge") or g_item.get("badge", f"🌟 ภาพโปรโมต #{g_num}")
                g_title = ov.get("title") or g_item.get("title", g_fname)
                g_sub = ov.get("subtitle") or g_item.get("subtitle", "")

                with g_cols[g_col_idx]:
                    with st.container(border=True):
                        render_html(
                            f'<div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:6px;"><span style="background:linear-gradient(135deg,#d32f2f,#ff5252);color:#ffffff;font-size:11.5px;font-weight:800;padding:4px 11px;border-radius:99px;">{g_badge}</span><span style="color:#8d6e63;font-size:12px;font-weight:800;">#{g_num:02d}/06</span></div><div style="color:#b71c1c;font-weight:800;font-size:16px;line-height:1.35;min-height:42px;">{g_title}</div><div style="color:#5C4033;font-size:12.8px;line-height:1.45;margin-top:4px;margin-bottom:8px;">{g_sub}</div>'
                        )
                        st.image(str(g_fpath), use_container_width=True)
                        if show_promo_zoom_dialog is not None:
                            if st.button(
                                f"🔍 คลิกขยายดูภาพใหญ่คมชัด (ภาพที่ {g_num})",
                                key=f"zoom_btn_{key_prefix}_{g_num}_{g_fname}",
                                use_container_width=True,
                            ):
                                show_promo_zoom_dialog(str(g_fpath), g_title, g_sub, g_badge)
                        else:
                            with st.expander(f"🔍 คลิกขยายดูภาพใหญ่คมชัด (ภาพที่ {g_num})"):
                                st.image(str(g_fpath), caption=g_title, use_container_width=True)

    # --------------------------------------------------------------------------
    # STEP 3: 🎬 วิดีโอที่ 2 (ปิดท้ายด้วยความจริงใจของทีมงานและโรงงาน)
    # --------------------------------------------------------------------------
    with st.container(border=True):
        render_html(
            f"""
<div style="background:linear-gradient(135deg,#064e3b 0%,#047857 55%,#059669 100%);border:2.5px solid #fde047;border-radius:18px;padding:14px 16px;color:#ffffff;margin-bottom:12px;box-shadow:0 8px 22px rgba(4,120,87,0.24);">
<div style="display:flex;justify-content:space-between;align-items:center;flex-wrap:wrap;gap:8px;margin-bottom:6px;">
<span style="background:#fef08a;color:#064e3b;font-weight:900;font-size:12px;padding:4px 12px;border-radius:99px;">🎬 STEP 3 • วิดีโอปิดท้ายด้วยความจริงใจของทีมงานและโรงงาน</span>
<span style="background:rgba(255,255,255,0.18);color:#fef08a;font-weight:800;font-size:12px;padding:4px 12px;border-radius:99px;border:1px solid #fde047;">🍦 100% Natural & Sincere Homemade Ice Cream</span>
</div>
<div style="font-family:'Kanit','Prompt',sans-serif;font-size:19px;font-weight:800;color:#ffffff;line-height:1.35;">{v2_title}</div>
<div style="font-size:13.5px;color:#ecfdf5;margin-top:4px;line-height:1.45;">{v2_sub}</div>
</div>
"""
        )

        v2_col_video, v2_col_fb = st.columns([1.15, 1.0])
        with v2_col_video:
            if v2_playable and (
                v2_playable.startswith("http") or Path(v2_playable).exists()
            ):
                try:
                    st.video(v2_playable)
                except Exception:
                    st.info("กำลังเตรียมสตรีมวิดีโอ 'ไอศกรีมที่จริงใจที่สุด' กรุณารอสักครู่...")
                render_html(
                    '<div style="text-align:center;color:#047857;font-size:12.5px;font-weight:800;margin-top:4px;">👆 กดปุ่ม ▶️ ด้านบนเพื่อรับชมวิดีโอ "ไอศกรีมที่จริงใจที่สุด" พร้อมเสียงได้ทันที!</div>'
                )
            else:
                st.info("กำลังประมวลผลวิดีโอ 'ไอศกรีมที่จริงใจที่สุด' สำหรับสตรีมมิง...")

        with v2_col_fb:
            render_html(
                f"""
<div style="background:linear-gradient(145deg,#fffbeb 0%,#fff1f2 60%,#fef3c7 100%);border:2.5px solid #d32f2f;border-radius:18px;padding:16px;color:#2B1810;box-shadow:0 8px 22px rgba(211,47,47,0.12);">
<div style="display:flex;align-items:center;justify-content:space-between;flex-wrap:wrap;gap:8px;margin-bottom:8px;">
<span style="background:#1877F2;color:#ffffff;font-weight:800;font-size:12px;padding:4px 12px;border-radius:99px;">📘 FACEBOOK OFFICIAL PAGE</span>
<span style="color:#b91c1c;font-size:12px;font-weight:800;">⭐ มาตรฐานโรงงานเดย์ไอศกรีม</span>
</div>
<div style="font-family:'Kanit','Prompt',sans-serif;font-size:18px;font-weight:800;color:#b71c1c;margin-bottom:6px;">📘 Dayicecream แฟรนไชส์ไอศครีมที่ดีที่สุด</div>
<div style="font-size:13.2px;color:#4A2C2A;line-height:1.55;margin-bottom:12px;">
• <b>ความจริงใจในทุกถ้วย:</b> คัดกะทิทับสะแกคั้นสด มะพร้าวน้ำหอมบ้านแพ้ว 100% นมโคสดแท้ และผลไม้สดตามฤดูกาล<br>
• <b>ไร้สารเคมี 100%:</b> ไม่ใส่นมผง ไม่ใส่แป้ง ไม่ใส่วัตถุกันเสีย และไม่ใช้อิมัลซิไฟเออร์<br>
• <b>การันตีความสำเร็จ:</b> เปิดร้านแฟรนไชส์กำไร 100% พร้อมระบบคืนเงินมัดจำตู้ 100% ตลอดอายุสัญญา 10 ปี เจ้าเดียวในไทย!
</div>
<a href="{v2_ext_url}" target="_blank" rel="noopener noreferrer" style="display:block;text-align:center;background:linear-gradient(135deg,#1877F2 0%,#1d4ed8 100%);color:#ffffff;font-weight:800;font-size:14px;padding:12px 16px;border-radius:14px;text-decoration:none;box-shadow:0 6px 18px rgba(24,119,242,0.3);margin-bottom:8px;">{v2_ext_label}</a>
<a href="{line_item.get('url', 'https://line.me/ti/p/BX7Fscqs71')}" target="_blank" rel="noopener noreferrer" style="display:block;text-align:center;background:linear-gradient(135deg,#059669 0%,#10b981 100%);color:#ffffff;font-weight:800;font-size:14px;padding:12px 16px;border-radius:14px;text-decoration:none;box-shadow:0 6px 18px rgba(16,185,129,0.28);">💬 ทัก LINE: Dayinterfood สั่งไอศกรีม / สมัครแฟรนไชส์ฟรี! ↗</a>
</div>
"""
            )


# ==============================================================================
# PAGE 1 (DEFAULT): 📍 1. ค้นหา 300+ สาขาใกล้บ้านคุณ (กดนำทางไปซื้อหน้าร้าน)
# ==============================================================================
if current_page == "branches":
    active_branches = (
        list(all_branches)
        if admin_mode
        else [b for b in all_branches if not b.get("is_internal")]
    )

    smart_branch_count_label = (
        "กว่า 300+ สาขาทั่วประเทศไทย"
        if len(active_branches) <= 300
        else f"{len(active_branches):,} สาขาทั่วประเทศไทย"
    )
    total_customers = 323499
    smart_banner_title = f"🙏 ขอขอบคุณลูกค้ากว่า {total_customers:,}+ ท่าน ที่อุดหนุน เดย์ ไอศกรีม ทุกสาขาทั่วประเทศ"
    smart_banner_sub = "ข้อมูลจริงจากฐานลูกค้าที่กดเข้าค้นหาแผนที่ร้านเดย์ไอศกรีมกว่า 300 สาขาทั่วไทย • ความสุขที่คุณสัมผัสได้ทุกวัน"

    render_html(
        f"""
<div class="brand-section-header">
<div style="display:flex;align-items:flex-start;gap:12px;">
<div style="width:44px;height:44px;border-radius:50%;background:#ffffff;color:#d32f2f;display:flex;align-items:center;justify-content:center;font-size:24px;flex-shrink:0;box-shadow:0 4px 10px rgba(0,0,0,0.16);border:2px solid #fde047;">🙏</div>
<div>
<div class="brand-section-title" style="font-size:20px;line-height:1.35;">{smart_banner_title}</div>
<div class="brand-section-sub" style="line-height:1.45;margin-top:4px;">{smart_banner_sub}</div>
</div>
</div>
<div style="display:flex;gap:8px;flex-wrap:wrap;align-items:center;margin-top:4px;">
<span style="background:#111827;color:#fef08a;padding:6px 13px;border-radius:99px;font-size:12.5px;font-weight:800;border:1.5px solid #fde047;">👁️ ดู {total_customers:,}+ ครั้ง</span>
<span style="background:#ffffff;color:#d32f2f;padding:6px 13px;border-radius:99px;font-size:12.5px;font-weight:800;">🍨 {smart_branch_count_label}</span>
</div>
</div>
"""
    )

    ctrl_col1, ctrl_col2 = st.columns([2.5, 1.5])
    with ctrl_col1:
        search_query = st.text_input(
            "🔍 ค้นหาจังหวัด / อำเภอ / เขต / ย่าน / ชื่อร้านใกล้บ้านคุณ",
            value="",
            placeholder="พิมพ์ค้นหา เช่น นครปฐม, กรุงเทพ, เชียงใหม่, พัทยา, บุรีรัมย์, หาดใหญ่, ศาลายา...",
        )
    with ctrl_col2:
        gps_btn_clicked = st.button(
            "📍 ค้นหาสาขาใกล้ฉันที่สุด (GPS)",
            key="btn_streamlit_gps_trigger",
            type="primary",
            use_container_width=True,
        )
        if gps_btn_clicked:
            ip_lat, ip_lon, ip_label = detect_approx_location_ip()
            st.session_state["gps_active"] = True
            st.session_state["gps_req_id"] = int(st.session_state.get("gps_req_id", 0)) + 1
            if st.session_state.get("user_loc_label") == "สำนักงานใหญ่ เดย์ไอศครีม (จ.นครปฐม)":
                st.session_state["user_lat"] = ip_lat
                st.session_state["user_lon"] = ip_lon
                st.session_state["user_loc_label"] = ip_label
            st.toast("📍 กำลังดึงพิกัด GPS มือถือของคุณและแสดงสาขาใกล้ที่สุดทันที!", icon="📍")

    with st.expander(
        "🧭 เลือกจังหวัดหรือโซนพื้นที่ของคุณ (กรณีไม่ได้เปิด GPS หรือเปิดใน TikTok กดเลือกโซนที่นี่ได้ทันที)",
        expanded=True,
    ):
        preset_locations = {
            "📍 ตำแหน่งปัจจุบันของคุณ (หรือสำนักงานใหญ่ จ.นครปฐม)": None,
            "🏭 นครปฐม (สำนักงานใหญ่ เดย์ไอศครีม อ.เมือง)": (13.8246901, 100.0570871),
            "🏙️ กรุงเทพมหานคร (สยาม / ประตูน้ำ / ใจกลางเมือง)": (13.7500, 100.5390),
            "🛍️ ศาลายา / ม.มหิดล (นครปฐม - กรุงเทพฯ ฝั่งธน)": (13.7944, 100.3256),
            "🌆 นนทบุรี / ปทุมธานี / รังสิต (ปริมณฑลโซนเหนือ)": (13.9130, 100.5500),
            "🏖️ พัทยา / ชลบุรี / ระยอง (ภาคตะวันออก)": (12.9236, 100.8825),
            "🏛️ อยุธยา / สระบุรี / ลพบุรี (ภาคกลาง)": (14.3532, 100.5684),
            "⛰️ เชียงใหม่ / ลำพูน / เชียงราย (ภาคเหนือ)": (18.7883, 98.9853),
            "🏰 นครราชสีมา / โคราช (ภาคอีสาน)": (14.9799, 102.0978),
            "⚡ บุรีรัมย์ / สุรินทร์ / ศรีสะเกษ (อีสานใต้)": (14.9930, 103.1029),
            "🌾 ขอนแก่น / อุดรธานี / มหาสารคาม (อีสานเหนือ)": (16.4419, 102.8360),
            "🌴 สุราษฎร์ธานี / พังงา / ภูเก็ต (ภาคใต้ตอนบน-อันดามัน)": (9.1382, 99.3217),
            "🌊 หาดใหญ่ / สงขลา / นครศรีธรรมราช (ภาคใต้ตอนล่าง)": (7.0086, 100.4747),
        }
        selected_preset = st.selectbox(
            "เลือกพื้นที่เพื่อจัดเรียงสาขาที่ใกล้คุณที่สุดทันที:",
            list(preset_locations.keys()),
        )
        if preset_locations[selected_preset] is not None:
            st.session_state["user_lat"], st.session_state["user_lon"] = preset_locations[
                selected_preset
            ]
            st.session_state["user_loc_label"] = selected_preset
            st.session_state["gps_active"] = True

    if search_query.strip():
        keywords = [k.strip().lower() for k in search_query.strip().split() if k.strip()]
        filtered_branches = []
        for b in active_branches:
            haystack = f"{b.get('name', '')} {b.get('description', '')} {' '.join(b.get('phones', []))}".lower()
            if all(kw in haystack for kw in keywords):
                filtered_branches.append(b)
    else:
        filtered_branches = list(active_branches)

    ref_lat = float(st.session_state["user_lat"])
    ref_lon = float(st.session_state["user_lon"])
    for b in filtered_branches:
        b_lat = float(b["lat"])
        b_lon = float(b["lon"])
        b["distance_km"] = round(haversine_km(ref_lat, ref_lon, b_lat, b_lon), 2)
        b["nav_url"] = (
            f"https://www.google.com/maps/dir/?api=1&destination={b_lat},{b_lon}&travelmode=driving"
        )
        b["search_url"] = f"https://www.google.com/maps/search/?api=1&query={b_lat},{b_lon}"

    filtered_branches.sort(key=lambda x: x["distance_km"])

    top_nearest_branch = filtered_branches[0] if filtered_branches else None
    top_nearest_nav_url = (
        top_nearest_branch["nav_url"]
        if top_nearest_branch
        else f"https://www.google.com/maps/dir/?api=1&destination={DEFAULT_HQ_LAT},{DEFAULT_HQ_LON}&travelmode=driving"
    )
    top_nearest_search_url = (
        top_nearest_branch["search_url"]
        if top_nearest_branch
        else f"https://www.google.com/maps/search/?api=1&query={DEFAULT_HQ_LAT},{DEFAULT_HQ_LON}"
    )

    # ==============================================================================
    # 🚀 TOP-LEVEL LIVE GPS & UNIVERSAL GOOGLE MAPS NAVIGATOR (Renders in Parent DOM via st.html)
    # - ปลดล็อก Iframe Sandbox ของแผนที่ Folium ให้กดลิงก์ทะลุออกไปยังแอป Google Maps ได้ 100%
    # - เรียกขอพิกัด GPS มือถือจริง (navigator.geolocation.getCurrentPosition) ทันทีเมื่อกดปุ่ม
    # - หากเปิดใน TikTok WebView ที่ปิดสิทธิ์ GPS จะไม่ค้างเด็ดขาด! มีปุ่มเลือกจังหวัด/โซนด่วน + ปุ่มเปิดแอป Google Maps ทันที
    # ==============================================================================
    live_gps_branches_json = json.dumps(
        [
            {
                "name": b["name"],
                "lat": b["lat"],
                "lon": b["lon"],
                "phones": b.get("phones", []),
                "nav_url": b["nav_url"],
                "search_url": b["search_url"],
            }
            for b in filtered_branches
        ],
        ensure_ascii=False,
    )
    gps_req_id_val = int(st.session_state.get("gps_req_id", 0))
    gps_auto_start_str = "true" if st.session_state.get("gps_active") else "false"
    current_loc_label_js = json.dumps(st.session_state.get("user_loc_label", "จุดอ้างอิงปัจจุบัน"), ensure_ascii=False)

    top_gps_navigator_html = f"""
    <style>
        .day-live-gps-box {{
            font-family: 'Prompt', 'Kanit', sans-serif;
            background: linear-gradient(145deg, #fffdf9 0%, #fff1f2 100%);
            border: 2.5px solid #ef4444;
            border-radius: 20px;
            padding: 14px 16px;
            margin: 6px 0 12px 0;
            box-shadow: 0 8px 24px rgba(211, 47, 47, 0.14);
        }}
        .day-live-gps-btn-row {{
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(220px, 1fr));
            gap: 10px;
            margin-top: 10px;
        }}
        .day-live-btn-primary {{
            display: flex;
            align-items: center;
            justify-content: center;
            gap: 6px;
            width: 100%;
            background: linear-gradient(135deg, #b91c1c 0%, #dc2626 55%, #ef4444 100%);
            color: #ffffff !important;
            border: 2px solid #fde047;
            border-radius: 14px;
            padding: 12px 14px;
            font-family: 'Prompt', 'Kanit', sans-serif;
            font-size: 14.5px;
            font-weight: 800;
            cursor: pointer;
            text-decoration: none !important;
            text-align: center;
            box-shadow: 0 6px 16px rgba(211, 47, 47, 0.28);
            transition: transform 0.15s ease;
            box-sizing: border-box;
        }}
        .day-live-btn-primary:hover {{
            transform: translateY(-1px);
        }}
        .day-live-btn-gmaps {{
            display: flex;
            align-items: center;
            justify-content: center;
            gap: 6px;
            width: 100%;
            background: linear-gradient(135deg, #15803d 0%, #16a34a 100%);
            color: #ffffff !important;
            border: 2px solid #bbf7d0;
            border-radius: 14px;
            padding: 12px 14px;
            font-family: 'Prompt', 'Kanit', sans-serif;
            font-size: 14.5px;
            font-weight: 800;
            cursor: pointer;
            text-decoration: none !important;
            text-align: center;
            box-shadow: 0 6px 16px rgba(22, 163, 74, 0.25);
            box-sizing: border-box;
        }}
        .day-live-btn-mapall {{
            display: flex;
            align-items: center;
            justify-content: center;
            gap: 6px;
            width: 100%;
            background: linear-gradient(135deg, #1e40af 0%, #2563eb 100%);
            color: #ffffff !important;
            border: 2px solid #bfdbfe;
            border-radius: 14px;
            padding: 12px 14px;
            font-family: 'Prompt', 'Kanit', sans-serif;
            font-size: 14px;
            font-weight: 800;
            cursor: pointer;
            text-decoration: none !important;
            text-align: center;
            box-shadow: 0 6px 16px rgba(37, 99, 235, 0.24);
            box-sizing: border-box;
        }}
        .day-zone-pills-wrap {{
            display: flex;
            flex-wrap: wrap;
            gap: 6px;
            margin-top: 10px;
            padding-top: 8px;
            border-top: 1.5px dashed #fca5a5;
        }}
        .day-zone-pill {{
            background: #ffffff;
            color: #b91c1c;
            border: 1.5px solid #fca5a5;
            border-radius: 999px;
            padding: 5px 11px;
            font-family: 'Prompt', 'Kanit', sans-serif;
            font-size: 12.5px;
            font-weight: 700;
            cursor: pointer;
            transition: all 0.15s ease;
        }}
        .day-zone-pill:hover, .day-zone-pill.active {{
            background: #dc2626;
            color: #ffffff;
            border-color: #dc2626;
        }}
        .day-live-cards-grid {{
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(240px, 1fr));
            gap: 10px;
            margin-top: 12px;
        }}
        .day-live-branch-card {{
            background: #ffffff;
            border: 2px solid #fecaca;
            border-radius: 14px;
            padding: 12px;
            box-shadow: 0 4px 12px rgba(211, 47, 47, 0.08);
            display: flex;
            flex-direction: column;
            justify-content: space-between;
        }}
    </style>

    <div class="day-live-gps-box" id="day-live-gps-panel">
        <div style="display:flex;align-items:center;justify-content:space-between;flex-wrap:wrap;gap:8px;">
            <div style="font-size:16.5px;font-weight:800;color:#b91c1c;">
                📍 ระบบค้นหาพิกัดร้านใกล้คุณ & นำทางด้วย Google Maps ทันที
            </div>
            <div id="day-top-gps-status" style="font-size:13px;font-weight:700;color:#15803d;background:#dcfce7;padding:4px 12px;border-radius:999px;border:1px solid #86efac;">
                ✅ พร้อมนำทางไปยังสาขาที่ใกล้คุณที่สุด
            </div>
        </div>

        <div class="day-live-gps-btn-row">
            <button type="button" id="day-trigger-gps-now-btn" class="day-live-btn-primary">
                📍 กดค้นหาพิกัด GPS มือถือของฉันตอนนี้
            </button>
            <a id="day-top-nearest-nav-btn"
               href="{top_nearest_nav_url}"
               target="_blank" rel="noopener noreferrer"
               class="day-live-btn-gmaps">
                🚗 กดนำทางไปสาขาใกล้สุดทันที (Google Maps) ↗
            </a>
            <a id="day-top-search-map-btn"
               href="{top_nearest_search_url}"
               target="_blank" rel="noopener noreferrer"
               class="day-live-btn-mapall">
                🗺️ เปิดดูหมุดพิกัดร้านบนแอป Google Maps ↗
            </a>
        </div>

        <div class="day-zone-pills-wrap">
            <span style="font-size:12.5px;font-weight:800;color:#7f1d1d;align-self:center;margin-right:4px;">
                🧭 หรือจิ้มเลือกโซนใกล้คุณทันที (ไม่ต้องเปิด GPS):
            </span>
            <button type="button" class="day-zone-pill" data-lat="13.8246901" data-lon="100.0570871" data-label="จ.นครปฐม (สำนักงานใหญ่)">🏭 นครปฐม</button>
            <button type="button" class="day-zone-pill" data-lat="13.7500" data-lon="100.5390" data-label="กรุงเทพมหานคร (ใจกลางเมือง)">🏙️ กรุงเทพฯ</button>
            <button type="button" class="day-zone-pill" data-lat="13.7944" data-lon="100.3256" data-label="ศาลายา / ฝั่งธนฯ">🛍️ ศาลายา/ฝั่งธนฯ</button>
            <button type="button" class="day-zone-pill" data-lat="13.9130" data-lon="100.5500" data-label="นนทบุรี / ปทุมธานี">🌆 นนทบุรี/ปทุมฯ</button>
            <button type="button" class="day-zone-pill" data-lat="12.9236" data-lon="100.8825" data-label="พัทยา / ชลบุรี / ระยอง">🏖️ ชลบุรี/พัทยา</button>
            <button type="button" class="day-zone-pill" data-lat="14.3532" data-lon="100.5684" data-label="อยุธยา / สระบุรี">🏛️ อยุธยา/สระบุรี</button>
            <button type="button" class="day-zone-pill" data-lat="18.7883" data-lon="98.9853" data-label="เชียงใหม่ / ภาคเหนือ">⛰️ เชียงใหม่</button>
            <button type="button" class="day-zone-pill" data-lat="14.9799" data-lon="102.0978" data-label="นครราชสีมา / โคราช">🏰 โคราช</button>
            <button type="button" class="day-zone-pill" data-lat="14.9930" data-lon="103.1029" data-label="บุรีรัมย์ / สุรินทร์">⚡ บุรีรัมย์/สุรินทร์</button>
            <button type="button" class="day-zone-pill" data-lat="16.4419" data-lon="102.8360" data-label="ขอนแก่น / อุดรธานี">🌾 ขอนแก่น/อุดรฯ</button>
            <button type="button" class="day-zone-pill" data-lat="9.1382" data-lon="99.3217" data-label="สุราษฎร์ธานี / ภูเก็ต">🌴 สุราษฎร์ฯ/ภูเก็ต</button>
            <button type="button" class="day-zone-pill" data-lat="7.0086" data-lon="100.4747" data-label="หาดใหญ่ / สงขลา">🌊 หาดใหญ่/สงขลา</button>
        </div>

        <div id="day-live-gps-results-wrap" style="margin-top:10px;">
            <div id="day-live-gps-results-title" style="font-size:14.5px;font-weight:800;color:#b91c1c;"></div>
            <div id="day-live-gps-cards" class="day-live-cards-grid"></div>
        </div>
    </div>

    <script>
        (function() {{
            const BRANCHES_LIST = {live_gps_branches_json};
            const INIT_LAT = {ref_lat};
            const INIT_LON = {ref_lon};
            const INIT_LABEL = {current_loc_label_js};
            const GPS_REQ_ID = {gps_req_id_val};
            const GPS_AUTO = {gps_auto_start_str};

            function unlockMapIframes() {{
                const iframes = document.querySelectorAll('iframe');
                for (let i = 0; i < iframes.length; i++) {{
                    const ifr = iframes[i];
                    try {{
                        ifr.setAttribute('allow', 'geolocation *; clipboard-write *');
                        if (ifr.hasAttribute('sandbox')) {{
                            const sb = ifr.getAttribute('sandbox') || '';
                            const needed = [
                                'allow-scripts',
                                'allow-same-origin',
                                'allow-popups',
                                'allow-popups-to-escape-sandbox',
                                'allow-top-navigation',
                                'allow-top-navigation-by-user-activation'
                            ];
                            let updated = sb;
                            for (let k = 0; k < needed.length; k++) {{
                                if (updated.indexOf(needed[k]) === -1) {{
                                    updated += ' ' + needed[k];
                                }}
                            }}
                            ifr.setAttribute('sandbox', updated.trim());
                        }}
                    }} catch (e) {{}}
                }}
            }}
            unlockMapIframes();
            setTimeout(unlockMapIframes, 600);
            setTimeout(unlockMapIframes, 1800);

            function haversineKm(lat1, lon1, lat2, lon2) {{
                const R = 6371.0;
                const dLat = (lat2 - lat1) * Math.PI / 180;
                const dLon = (lon2 - lon1) * Math.PI / 180;
                const a = Math.sin(dLat / 2) * Math.sin(dLat / 2) +
                          Math.cos(lat1 * Math.PI / 180) * Math.cos(lat2 * Math.PI / 180) *
                          Math.sin(dLon / 2) * Math.sin(dLon / 2);
                return 2 * R * Math.asin(Math.sqrt(a));
            }}

            function syncFoliumMap(lat, lon, labelText) {{
                unlockMapIframes();
                const iframes = document.querySelectorAll('iframe');
                for (let i = 0; i < iframes.length; i++) {{
                    try {{
                        const cw = iframes[i].contentWindow;
                        if (cw && typeof cw.highlightNearestFrom === 'function') {{
                            cw.highlightNearestFrom(lat, lon, labelText);
                        }}
                    }} catch (e) {{}}
                }}
            }}

            function renderNearestBranchesTop(lat, lon, labelText) {{
                if (!BRANCHES_LIST || !BRANCHES_LIST.length) return;
                const ranked = BRANCHES_LIST.map(function(b) {{
                    return {{
                        name: b.name,
                        lat: b.lat,
                        lon: b.lon,
                        phones: b.phones || [],
                        nav_url: 'https://www.google.com/maps/dir/?api=1&destination=' + b.lat + ',' + b.lon + '&travelmode=driving',
                        search_url: 'https://www.google.com/maps/search/?api=1&query=' + b.lat + ',' + b.lon,
                        km: haversineKm(lat, lon, b.lat, b.lon)
                    }};
                }}).sort(function(a, b) {{ return a.km - b.km; }});

                const nearest = ranked[0];
                const topNavBtn = document.getElementById('day-top-nearest-nav-btn');
                const topSearchBtn = document.getElementById('day-top-search-map-btn');
                if (topNavBtn && nearest) {{
                    topNavBtn.href = nearest.nav_url;
                    topNavBtn.innerHTML = '🚗 นำทางไปสาขาใกล้สุด (' + nearest.km.toFixed(1) + ' กม.) Google Maps ↗';
                }}
                if (topSearchBtn && nearest) {{
                    topSearchBtn.href = nearest.search_url;
                }}

                const titleEl = document.getElementById('day-live-gps-results-title');
                const cardsEl = document.getElementById('day-live-gps-cards');
                if (titleEl) {{
                    titleEl.innerHTML = '🎯 4 อันดับสาขาที่ใกล้ที่สุดจาก: <span style="color:#15803d;">' + labelText + '</span> (กดปุ่มสีแดงเพื่อเปิดแอป Google Maps นำทางทันที)';
                }}
                if (cardsEl) {{
                    cardsEl.innerHTML = ranked.slice(0, 4).map(function(b, idx) {{
                        const rawPhone = (b.phones && b.phones.length) ? b.phones[0].replace(/[^0-9+]/g, '') : '0863328091';
                        const phoneLabel = (b.phones && b.phones.length) ? b.phones[0] : '086-3328091';
                        return '<div class="day-live-branch-card">' +
                            '<div>' +
                                '<div style="display:flex;justify-content:space-between;align-items:center;gap:6px;margin-bottom:6px;">' +
                                    '<span style="background:#dc2626;color:#fff;font-size:11.5px;font-weight:800;padding:2px 9px;border-radius:999px;">อันดับ #' + (idx + 1) + ' ใกล้คุณ</span>' +
                                    '<span style="background:#f0fdf4;color:#15803d;border:1px solid #86efac;font-size:12px;font-weight:800;padding:2px 8px;border-radius:999px;">📏 ' + b.km.toFixed(2) + ' กม.</span>' +
                                '</div>' +
                                '<div style="font-size:14.5px;font-weight:800;color:#2B1810;line-height:1.35;margin-bottom:4px;">📍 ' + b.name + '</div>' +
                                '<div style="font-size:12.5px;font-weight:700;color:#b91c1c;margin-bottom:8px;">📞 โทร: ' + phoneLabel + '</div>' +
                            '</div>' +
                            '<div style="display:grid;grid-template-columns:1fr;gap:6px;">' +
                                '<a href="' + b.nav_url + '" target="_blank" rel="noopener noreferrer" ' +
                                   'style="display:block;text-align:center;background:linear-gradient(135deg,#d32f2f,#ff5252);color:#ffffff;font-weight:800;font-size:13px;padding:9px 10px;border-radius:10px;text-decoration:none;box-shadow:0 4px 10px rgba(211,47,47,0.22);">' +
                                   '📍 กดนำทางไปสาขานี้ (Google Maps)' +
                                '</a>' +
                                '<div style="display:grid;grid-template-columns:1fr 1fr;gap:6px;">' +
                                    '<a href="tel:' + rawPhone + '" style="display:block;text-align:center;background:#059669;color:#ffffff;font-weight:700;font-size:12px;padding:6px 8px;border-radius:8px;text-decoration:none;">📞 โทรติดต่อ</a>' +
                                    '<a href="' + b.search_url + '" target="_blank" rel="noopener noreferrer" style="display:block;text-align:center;background:#eff6ff;color:#1d4ed8;border:1px solid #93c5fd;font-weight:700;font-size:12px;padding:6px 8px;border-radius:8px;text-decoration:none;">🗺️ ดูหมุดแผนที่</a>' +
                                '</div>' +
                            '</div>' +
                        '</div>';
                    }}).join('');
                }}
                syncFoliumMap(lat, lon, labelText);
            }}

            window.triggerDayTopGPS = function() {{
                const statusEl = document.getElementById('day-top-gps-status');
                if (statusEl) {{
                    statusEl.style.background = '#fef9c3';
                    statusEl.style.color = '#854d0e';
                    statusEl.style.borderColor = '#fde047';
                    statusEl.innerHTML = '⏳ กำลังดึงพิกัด GPS มือถือของคุณ...';
                }}
                if (navigator.geolocation) {{
                    navigator.geolocation.getCurrentPosition(
                        function(pos) {{
                            const lat = pos.coords.latitude;
                            const lon = pos.coords.longitude;
                            try {{
                                sessionStorage.setItem('day_gps_lat', String(lat));
                                sessionStorage.setItem('day_gps_lon', String(lon));
                            }} catch (e) {{}}
                            if (statusEl) {{
                                statusEl.style.background = '#dcfce7';
                                statusEl.style.color = '#15803d';
                                statusEl.style.borderColor = '#86efac';
                                statusEl.innerHTML = '✅ พบพิกัด GPS ของคุณแล้ว! กดปุ่มนำทางได้ทันที';
                            }}
                            renderNearestBranchesTop(lat, lon, 'พิกัด GPS ปัจจุบันของคุณ');
                        }},
                        function(err) {{
                            if (statusEl) {{
                                statusEl.style.background = '#fff1f2';
                                statusEl.style.color = '#b91c1c';
                                statusEl.style.borderColor = '#fca5a5';
                                statusEl.innerHTML = '🧭 เลือกโซนจังหวัดด้านล่าง หรือกดปุ่มนำทาง Google Maps ได้ทันที';
                            }}
                            renderNearestBranchesTop(INIT_LAT, INIT_LON, INIT_LABEL);
                        }},
                        {{ enableHighAccuracy: true, timeout: 4000, maximumAge: 60000 }}
                    );
                }} else {{
                    if (statusEl) {{
                        statusEl.innerHTML = '🧭 เลือกโซนจังหวัดด้านล่าง หรือกดปุ่มนำทาง Google Maps ได้ทันที';
                    }}
                    renderNearestBranchesTop(INIT_LAT, INIT_LON, INIT_LABEL);
                }}
            }};

            const gpsBtn = document.getElementById('day-trigger-gps-now-btn');
            if (gpsBtn) {{
                gpsBtn.addEventListener('click', function() {{
                    window.triggerDayTopGPS();
                }});
            }}

            const topMenuBtn1 = document.querySelector('.st-key-nav_btn_branches button');
            if (topMenuBtn1 && !topMenuBtn1.dataset.dayGpsBound) {{
                topMenuBtn1.dataset.dayGpsBound = '1';
                topMenuBtn1.addEventListener('click', function() {{
                    window.triggerDayTopGPS();
                }});
            }}

            const stGpsBtn = document.querySelector('.st-key-btn_streamlit_gps_trigger button');
            if (stGpsBtn && !stGpsBtn.dataset.dayGpsBound) {{
                stGpsBtn.dataset.dayGpsBound = '1';
                stGpsBtn.addEventListener('click', function() {{
                    window.triggerDayTopGPS();
                }});
            }}

            const pills = document.querySelectorAll('.day-zone-pill');
            for (let i = 0; i < pills.length; i++) {{
                pills[i].addEventListener('click', function() {{
                    for (let j = 0; j < pills.length; j++) pills[j].classList.remove('active');
                    this.classList.add('active');
                    const zLat = parseFloat(this.getAttribute('data-lat'));
                    const zLon = parseFloat(this.getAttribute('data-lon'));
                    const zLabel = this.getAttribute('data-label') || 'โซนที่เลือก';
                    const statusEl = document.getElementById('day-top-gps-status');
                    if (statusEl) {{
                        statusEl.style.background = '#dcfce7';
                        statusEl.style.color = '#15803d';
                        statusEl.style.borderColor = '#86efac';
                        statusEl.innerHTML = '📍 แสดงสาขาใกล้: ' + zLabel;
                    }}
                    renderNearestBranchesTop(zLat, zLon, zLabel);
                }});
            }}

            // แสดงการ์ดสาขาใกล้สุดทันทีโดยไม่ค้าง และหากเคยได้พิกัด GPS หรือกดปุ่มค้นหา GPS ให้เรียกพิกัดทันที
            let savedLat = null;
            let savedLon = null;
            try {{
                savedLat = parseFloat(sessionStorage.getItem('day_gps_lat'));
                savedLon = parseFloat(sessionStorage.getItem('day_gps_lon'));
            }} catch (e) {{}}

            if (savedLat && savedLon && !isNaN(savedLat) && !isNaN(savedLon)) {{
                renderNearestBranchesTop(savedLat, savedLon, 'พิกัด GPS มือถือของคุณ');
            }} else {{
                renderNearestBranchesTop(INIT_LAT, INIT_LON, INIT_LABEL);
            }}

            if (GPS_REQ_ID > 0 && window._lastDayGpsReqId !== GPS_REQ_ID) {{
                window._lastDayGpsReqId = GPS_REQ_ID;
                setTimeout(function() {{
                    window.triggerDayTopGPS();
                }}, 120);
            }}
        }})();
    </script>
    """
    st.html(top_gps_navigator_html, unsafe_allow_javascript=True)

    thailand_map_html = build_thailand_branch_map(
        branches=filtered_branches,
        ref_lat=ref_lat,
        ref_lon=ref_lon,
        gps_active=st.session_state["gps_active"],
        loc_label=st.session_state["user_loc_label"],
        pin_public_uri=CUSTOM_PIN_DATA_URI,
        pin_internal_uri=CUSTOM_PIN_INTERNAL_DATA_URI,
        search_active=bool(search_query.strip()),
    )
    components.html(
        thailand_map_html,
        height=640 if st.session_state["gps_active"] else 520,
        scrolling=False,
    )

    render_html(
        f"""
<div style="display:flex;align-items:center;justify-content:space-between;flex-wrap:wrap;margin:14px 0 10px 0;">
<div style="font-size:19px;font-weight:800;color:#b71c1c;display:flex;align-items:center;gap:8px;">
<span>🍨 สาขาเดย์ไอศครีมที่อยู่ใกล้คุณที่สุด (เรียงตามระยะทางจริง)</span>
</div>
<div style="color:#5C4033;font-size:13px;">📍 เรียงตามระยะทางใกล้สุดจาก: <b style="color:#d32f2f;">{st.session_state['user_loc_label']}</b></div>
</div>
"""
    )

    if not filtered_branches:
        st.warning("ไม่พบสาขาที่ตรงกับคำค้นหา กรุณาลองพิมพ์ชื่อจังหวัด อำเภอ หรือย่านใกล้เคียงครับ")
    else:
        show_limit_choice = st.radio(
            "เลือกรูปแบบการแสดงการ์ดสาขาด้านล่าง:",
            options=[10, 24, 50, 9999],
            index=0,
            horizontal=True,
            format_func=lambda x: {
                10: "🍦 10 อันดับใกล้ฉัน",
                24: "🍨 24 อันดับใกล้ฉัน",
                50: "🗺️ 50 อันดับใกล้ฉัน",
                9999: f"👑 ทุกสาขา ({smart_branch_count_label})",
            }[x],
        )
        show_limit = min(int(show_limit_choice), len(filtered_branches))

        cols_per_row = 2 if show_limit_choice == 10 else 3
        displayed_branches = filtered_branches[:show_limit]
        for row_start in range(0, len(displayed_branches), cols_per_row):
            row_items = displayed_branches[row_start : row_start + cols_per_row]
            cols = st.columns(cols_per_row)
            for col_idx, branch in enumerate(row_items):
                rank_num = row_start + col_idx + 1
                is_int = branch.get("is_internal", False)
                card_cls = "branch-card branch-card-internal" if is_int else "branch-card"
                status_html = (
                    f'<span style="background:#d32f2f;color:#ffffff;font-weight:800;font-size:11.5px;padding:4px 11px;border-radius:99px;">สถานะภายใน ({", ".join(branch.get("internal_tags", []))})</span>'
                    if is_int
                    else f'<span style="background:#16a34a;color:#ffffff;font-weight:800;font-size:11.5px;padding:4px 11px;border-radius:99px;">🍦 อันดับ #{rank_num} ใกล้คุณ</span>'
                )
                phones = branch.get("phones", [])
                dial_phone = (
                    re.sub(r"[^0-9+]", "", phones[0]) if phones else "0863328091"
                )
                if not dial_phone:
                    dial_phone = "0863328091"
                phone_str = (
                    f'<div style="color:#d32f2f;font-size:13px;font-weight:700;margin-top:6px;">📞 เบอร์สาขา: {", ".join(phones)}</div>'
                    if phones
                    else '<div style="color:#8d6e63;font-size:12.5px;font-weight:600;margin-top:6px;">📞 ศูนย์บริการสาขา: 086-3328091</div>'
                )
                desc_short = branch.get("description", "")
                if len(desc_short) > 135:
                    desc_short = desc_short[:135] + "..."
                if not desc_short:
                    desc_short = "จุดจำหน่ายไอศกรีมกะทิสดและไอศกรีมโฮมเมดหลากรสชาติ เดย์ไอศครีม (Day Ice Cream)"

                maps_url = f"https://www.google.com/maps/dir/?api=1&destination={branch['lat']},{branch['lon']}&travelmode=driving"

                # ดีไซน์การ์ดสาขา 3 แถวคลีนๆ + ปุ่ม st.link_button มาตรฐาน Streamlit เด้งเปิดแอป Google Maps ทันที 100%
                with cols[col_idx]:
                    render_html(
                        f'<div class="{card_cls}" style="margin-bottom:6px;"><div><div style="display:flex;justify-content:space-between;align-items:center;gap:6px;margin-bottom:10px;">{status_html}<span style="background:#fff1f2;border:1.5px solid #fca5a5;color:#d32f2f;font-weight:800;font-size:12.5px;padding:4px 11px;border-radius:99px;">📏 ห่าง {branch.get("distance_km", 0):.2f} กม.</span></div><div><div style="color:#2B1810;font-weight:800;font-size:16.5px;line-height:1.35;">📍 {branch.get("name")}</div><div style="color:#5C4033;font-size:13px;line-height:1.45;margin-top:5px;">{desc_short}</div>{phone_str}</div></div><div class="branch-actions-row"><a class="branch-call-btn" href="tel:{dial_phone}">📞 โทรติดต่อสาขา</a><a class="branch-nav-btn" href="{maps_url}" target="_blank" rel="noopener noreferrer">🚗 กดนำทางด้วย Google Maps</a></div></div>'
                    )
                    st.link_button(
                        "📍 กดนำทางไปสาขานี้ (Google Maps)",
                        url=maps_url,
                        use_container_width=True,
                        type="primary",
                    )

    st.markdown("---")
    # 🏆 2. ผสมผสานโซน "มาตรฐาน Michelin Guide กว่า 10 สาขา & ลูกค้ากว่า 323,499 คน" ไว้ต่อท้ายหน้าแรก (Home / แผนที่สาขา) ทันที!
    render_clean_michelin_gallery(key_prefix="page1_funnel", show_top_cta=False)




# ==============================================================================
# PAGE 2: 🍨 2. สั่งไอศกรีมออนไลน์ส่งถึงบ้าน (จิ้มเลือก 30 รสชาติ • โปร 22 / 44 / 105 ถ้วย ส่งฟรี!)
# ==============================================================================
elif current_page == "order_home":
    render_html(
        """
<div class="brand-section-header">
<div>
<div class="brand-section-title">🍨 สั่งไอศกรีมส่งตรงถึงบ้าน & ยกกล่องทั่วประเทศ (เลือกได้ 30 รสชาติ)</div>
<div class="brand-section-sub">จัดส่งฟรีทั่วประเทศไทย ได้รับของวันถัดไป • แพ็กด้วยน้ำแข็งแห้งมาตรฐานส่งออก การันตีหากละลายส่งใหม่ให้ฟรี 100%!</div>
</div>
<div>
<span style="background:#ffffff;color:#d32f2f;padding:6px 14px;border-radius:99px;font-size:13px;font-weight:800;">🛒 เลือกครบปุ๊บ ส่งออเดอร์เข้า LINE & Facebook ทันที</span>
</div>
</div>
"""
    )

    # ป้ายสิทธิพิเศษสมาชิก VIP เดย์ไอศกรีม (VIP Auto-Save & Repeat Order)
    render_html(
        """
<div style="background:linear-gradient(135deg,#78350f 0%,#b45309 45%,#d97706 100%);border:2.5px solid #fde047;border-radius:18px;padding:14px 18px;margin-bottom:14px;color:#ffffff;box-shadow:0 8px 24px rgba(180,83,9,0.24);display:flex;align-items:center;gap:12px;flex-wrap:wrap;">
<div style="font-size:30px;line-height:1;">👑</div>
<div style="flex:1;min-width:240px;">
<div style="font-size:15.5px;font-weight:800;color:#fef08a;line-height:1.38;">👑 สิทธิพิเศษสมาชิก VIP เดย์ไอศกรีม: ระบบจดจำที่อยู่จัดส่งและรสชาติโปรดของคุณไว้สำหรับการสั่งซื้อครั้งถัดไปอัตโนมัติ + รับสิทธิ์โปรโมชันพิเศษก่อนใคร!</div>
<div style="font-size:12.5px;color:#fffbeb;margin-top:3px;font-weight:600;">ไม่ต้องตั้งรหัสผ่าน • ระบบจำชื่อ เบอร์โทร ที่อยู่ และรสชาติที่คุณชอบไว้ให้อัตโนมัติ (กดดึงข้อมูลสั่งซ้ำได้ใน 1 คลิก)</div>
</div>
</div>
"""
    )

    # โหลดข้อมูลสมาชิก VIP อัตโนมัติเมื่อเปิดหน้าสั่งซื้อครั้งแรก (จาก query_params หรือฐานข้อมูล VIP ล่าสุด)
    if not st.session_state.get("vip_auto_loaded_init"):
        st.session_state["vip_auto_loaded_init"] = True
        qp_phone = ""
        try:
            qp_phone = str(st.query_params.get("vip_phone", "") or "").strip()
        except Exception:
            pass
        latest_vip = find_latest_vip_order(qp_phone)
        if latest_vip:
            if not st.session_state.get("mm_cust_name"):
                val_n = (latest_vip.get("ชื่อผู้รับ") or "").strip()
                if val_n and val_n != "(ไม่ระบุชื่อ)":
                    st.session_state["mm_cust_name"] = val_n
            if not st.session_state.get("mm_cust_phone"):
                val_p = (latest_vip.get("เบอร์โทรศัพท์") or "").strip()
                if val_p and val_p != "(ไม่ระบุเบอร์โทร)":
                    st.session_state["mm_cust_phone"] = val_p
            if not st.session_state.get("mm_cust_addr"):
                val_a = (latest_vip.get("ที่อยู่จัดส่ง") or "").strip()
                if val_a and val_a != "(ไม่ระบุที่อยู่)":
                    st.session_state["mm_cust_addr"] = val_a

    with st.container(border=True):
        vip_col1, vip_col2 = st.columns([1.8, 1.4])
        with vip_col1:
            vip_lookup_phone = st.text_input(
                "👑 สมาชิก VIP ที่เคยสั่งซื้อแล้ว: พิมพ์เบอร์โทรศัพท์เพื่อดึงที่อยู่ & รสชาติโปรดครั้งล่าสุด (ไม่ต้องใช้รหัสผ่าน)",
                value=st.session_state.get("mm_cust_phone", ""),
                placeholder="พิมพ์เบอร์โทร เช่น 081-234-5678 หรือเว้นว่างเพื่อดึงออเดอร์ล่าสุดในเครื่องนี้...",
                key="vip_lookup_phone_input",
            )
        with vip_col2:
            st.markdown("<div style='height:6px;'></div>", unsafe_allow_html=True)
            if st.button(
                "🔄 ดึงที่อยู่ & รสชาติโปรดครั้งล่าสุดอัตโนมัติ (Repeat VIP Order)",
                key="btn_vip_repeat_order",
                type="primary",
                use_container_width=True,
            ):
                matched_vip = find_latest_vip_order(vip_lookup_phone)
                if matched_vip:
                    v_name = (matched_vip.get("ชื่อผู้รับ") or "").strip()
                    v_phone = (matched_vip.get("เบอร์โทรศัพท์") or "").strip()
                    v_addr = (matched_vip.get("ที่อยู่จัดส่ง") or "").strip()
                    v_pkg = (matched_vip.get("รหัสแพ็กเกจ") or "").strip()
                    v_flv_json = matched_vip.get("flavors_json") or "{}"
                    if v_name and v_name != "(ไม่ระบุชื่อ)":
                        st.session_state["mm_cust_name"] = v_name
                    if v_phone and v_phone != "(ไม่ระบุเบอร์โทร)":
                        st.session_state["mm_cust_phone"] = v_phone
                    if v_addr and v_addr != "(ไม่ระบุที่อยู่)":
                        st.session_state["mm_cust_addr"] = v_addr
                    if v_pkg in ("PKG_A", "PKG_B", "PKG_C"):
                        st.session_state["pkg_radio_choice"] = v_pkg
                    try:
                        saved_flv_map = json.loads(v_flv_json)
                        if isinstance(saved_flv_map, dict):
                            for f in flavors_list:
                                fid_str = str(f["id"])
                                st.session_state[f"qty_flv_{f['id']}"] = int(
                                    saved_flv_map.get(fid_str, 0)
                                )
                    except Exception:
                        pass
                    st.toast(
                        f"👑 ดึงข้อมูลสมาชิก VIP ของ {v_name or v_phone} และรสชาติโปรดเรียบร้อยแล้ว!",
                        icon="👑",
                    )
                    st.rerun()
                else:
                    st.warning("ยังไม่มีประวัติการสั่งซื้อสำหรับเบอร์นี้ กรุณาเลือกรสชาติและกรอกที่อยู่ด้านล่างเพื่อบันทึกเป็นสมาชิก VIP ครั้งแรกครับ")

    st.markdown("#### 🎯 ขั้นตอนที่ 1: เลือกชุดโปรโมชันสุดคุ้มที่ต้องการสั่งซื้อ")

    pkg_choice = st.radio(
        "เลือก 1 ใน 3 แพ็กเกจยอดนิยม (ส่งฟรีทั่วประเทศไทย ได้รับของวันถัดไป การันตีหากละลายส่งใหม่ให้ฟรี!):",
        options=["PKG_A", "PKG_B", "PKG_C"],
        key="pkg_radio_choice",
        format_func=lambda x: {
            "PKG_A": "🎁 แพ็กเกจ A: ชุดอิ่มสุขใจ 22 ถ้วย = 990 บาท (เฉลี่ยถ้วยละ 45.- | ส่งฟรีทั่วประเทศ ได้รับวันถัดไป การันตีละลายเคลมฟรี!)",
            "PKG_B": "🥳 แพ็กเกจ B: ชุดปาร์ตี้สุดคุ้ม 44 ถ้วย = 1,500 บาท (เฉลี่ยถ้วยละ 34.- | ส่งฟรีทั่วประเทศ ได้รับวันถัดไป การันตีละลายเคลมฟรี!)",
            "PKG_C": "📦 แพ็กเกจ C: ชุดยกกล่อง 5 ออนซ์ (105 ถ้วย/กล่อง) = 3,150 บาท (ราคาพิเศษถ้วยละ 30 บาท! ฟรีน้ำแข็งแห้ง + ฟรีค่าส่งมูลค่า 900 บาททั่วประเทศ)",
        }[x],
    )

    num_boxes_c = 1
    add_foam_box_c = False
    foam_box_cost = 0

    if pkg_choice == "PKG_A":
        target_cups = 22
        base_price = 990
        pkg_title = "แพ็กเกจ A: ชุดอิ่มสุขใจ 22 ถ้วย (990 บาท ส่งฟรีทั่วไทย)"
        pkg_note = "ส่งฟรีทั่วประเทศไทย ได้รับของวันถัดไป การันตีหากละลายส่งใหม่ให้ฟรี!"
    elif pkg_choice == "PKG_B":
        target_cups = 44
        base_price = 1500
        pkg_title = "แพ็กเกจ B: ชุดปาร์ตี้สุดคุ้ม 44 ถ้วย (1,500 บาท ส่งฟรีทั่วไทย)"
        pkg_note = "ส่งฟรีทั่วประเทศไทย ได้รับของวันถัดไป การันตีหากละลายส่งใหม่ให้ฟรี!"
    else:
        c_col1, c_col2 = st.columns([1.2, 1.8])
        with c_col1:
            num_boxes_c = st.number_input(
                "📦 เลือกจำนวนกล่อง (กล่องละ 105 ถ้วย = 3,150 บาท):",
                min_value=1,
                max_value=20,
                value=1,
                step=1,
            )
        with c_col2:
            add_foam_box_c = st.checkbox(
                f"📦 รับกล่องโฟมเก็บความเย็นเพิ่ม (+100 บาท/กล่อง = +{100 * num_boxes_c:,} บาท)",
                value=False,
            )
        target_cups = 105 * int(num_boxes_c)
        foam_box_cost = (100 * int(num_boxes_c)) if add_foam_box_c else 0
        base_price = (3150 * int(num_boxes_c)) + foam_box_cost
        pkg_title = (
            f"แพ็กเกจ C: ชุดยกกล่อง 5 ออนซ์ จำนวน {num_boxes_c} กล่อง ({target_cups} ถ้วย)"
            + (f" + กล่องโฟมเก็บความเย็น {num_boxes_c} กล่อง" if add_foam_box_c else "")
        )
        pkg_note = "ราคาพิเศษถ้วยละ 30 บาท! ฟรีน้ำแข็งแห้ง + ฟรีค่าส่งมูลค่า 900 บาททั่วประเทศ (จัดส่งจันทร์–ศุกร์ ได้รับวันถัดไป)"

    current_selected_cups = sum(
        int(st.session_state.get(f"qty_flv_{f['id']}", 0))
        for f in flavors_list
        if not f.get("out_of_stock")
    )
    remaining_cups = target_cups - current_selected_cups

    st.markdown(
        f"#### 🍨 ขั้นตอนที่ 2: จิ้มเลือกรสชาติให้ครบ **{target_cups} ถ้วย** (พร้อมขาย {available_flavors_count} รส | สินค้าหมดชั่วคราว {oos_flavors_count} รส)"
    )

    btn_col1, btn_col2, btn_col3 = st.columns([1.4, 1.4, 2.2])
    with btn_col1:
        if st.button(
            f"⚡ จัดรสฮิตให้อัตโนมัติจนครบ {target_cups} ถ้วย",
            use_container_width=True,
            type="primary",
        ):
            avail_ids = [f["id"] for f in flavors_list if not f.get("out_of_stock")]
            if avail_ids:
                if current_selected_cups >= target_cups:
                    for fid in avail_ids:
                        st.session_state[f"qty_flv_{fid}"] = 0
                    need = target_cups
                else:
                    need = target_cups - current_selected_cups
                idx_cursor = 0
                while need > 0:
                    fid = avail_ids[idx_cursor % len(avail_ids)]
                    st.session_state[f"qty_flv_{fid}"] = (
                        int(st.session_state.get(f"qty_flv_{fid}", 0)) + 1
                    )
                    need -= 1
                    idx_cursor += 1
                st.rerun()

    with btn_col2:
        if st.button("🗑️ ล้างจำนวนที่เลือกทั้งหมด (เริ่มนับ 0 ใหม่)", use_container_width=True):
            for f in flavors_list:
                st.session_state[f"qty_flv_{f['id']}"] = 0
            st.rerun()

    with btn_col3:
        render_html(
            f'<div style="background:linear-gradient(135deg,#d32f2f,#ff5252);border-radius:14px;padding:12px 18px;display:flex;justify-content:space-between;align-items:center;color:#ffffff;box-shadow:0 6px 16px rgba(211,47,47,0.18);"><span style="font-size:14.5px;font-weight:700;">💰 ยอดรวมแพ็กเกจสุทธิ:</span><span style="font-size:20px;font-weight:800;">{base_price:,} บาท (ส่งฟรี!)</span></div>'
        )

    progress_ratio = min(1.0, max(0.0, current_selected_cups / float(target_cups)))
    st.progress(progress_ratio)

    if remaining_cups > 0:
        st.info(
            f"📊 **ตะกร้าไอศกรีมของคุณ:** เลือกแล้ว **{current_selected_cups} / {target_cups} ถ้วย** — กรุณาจิ้มเลือกรสชาติเพิ่มอีก **{remaining_cups} ถ้วย** ให้ครบตามโปรโมชันครับ"
        )
    elif remaining_cups < 0:
        st.error(
            f"⚠️ **เลือกเกินจำนวนโปรโมชัน:** ขณะนี้เลือกไว้ **{current_selected_cups} / {target_cups} ถ้วย** (เกินมา **{abs(remaining_cups)} ถ้วย**) — กรุณาลดจำนวนลง **{abs(remaining_cups)} ถ้วย** เพื่อให้ตรงตามแพ็กเกจครับ"
        )
    else:
        st.success(
            f"🎉 **เลือกครบ {target_cups} / {target_cups} ถ้วย เป๊ะตามโปรโมชันแล้ว!** เลื่อนลงไปกรอกชื่อ-ที่อยู่และกดส่งบิลเข้า LINE หรือ Facebook ด้านล่างได้เลยครับ"
        )

    view_mode_col1, view_mode_col2 = st.columns([1.4, 2.6])
    with view_mode_col1:
        render_html(
            '<div style="font-size:14.5px;font-weight:800;color:#8B0000;padding-top:6px;">🖼️ รูปแบบภาพสินค้าทั้ง 30 รสชาติ (ถ้วย 5 ออนซ์):</div>'
        )
    with view_mode_col2:
        flavor_img_mode = st.radio(
            "รูปแบบภาพไอศกรีม 30 รสชาติ",
            options=[
                "✨ ป้ายสติกเกอร์คู่ถ้วยจริง 5oz",
                "🏷️ ป้ายสติกเกอร์อ่านง่าย",
                "🍨 ถ้วยจริง 5oz",
            ],
            index=0,
            horizontal=True,
            label_visibility="collapsed",
            key="flavor_display_img_mode",
        )

    cols_per_row = 3 if flavor_img_mode == "✨ ป้ายสติกเกอร์คู่ถ้วยจริง 5oz" else 5
    for row_start in range(0, len(flavors_list), cols_per_row):
        row_flavors = flavors_list[row_start : row_start + cols_per_row]
        f_cols = st.columns(cols_per_row)
        for c_idx, flv in enumerate(row_flavors):
            fid = flv["id"]
            fname = flv["name"]
            fbadge = (flv.get("badge") or "").strip()
            is_oos = bool(flv.get("out_of_stock", False))
            cur_qty = int(st.session_state.get(f"qty_flv_{fid}", 0))
            if flavor_img_mode == "🏷️ ป้ายสติกเกอร์อ่านง่าย":
                thumb_str = flv.get("sticker_image") or flv.get("thumb_image", "")
            elif flavor_img_mode == "🍨 ถ้วยจริง 5oz":
                thumb_str = flv.get("cup_image") or flv.get("thumb_image", "")
            else:
                thumb_str = flv.get("combo_image") or flv.get("thumb_image", "")

            if is_oos:
                badge_html = '<span style="background:#94a3b8;color:#ffffff;font-size:11px;font-weight:800;padding:3px 9px;border-radius:99px;">❌ สินค้าหมดชั่วคราว</span>'
            elif "ขายดี" in fbadge:
                lbl = fbadge if "🔥" in fbadge else f"🔥 {fbadge}"
                badge_html = f'<span style="background:#d32f2f;color:#ffffff;font-size:11px;font-weight:800;padding:3px 9px;border-radius:99px;">{lbl}</span>'
            elif fbadge:
                lbl = fbadge if "⭐" in fbadge else f"⭐ {fbadge}"
                badge_html = f'<span style="background:#d97706;color:#ffffff;font-size:11px;font-weight:800;padding:3px 9px;border-radius:99px;">{lbl}</span>'
            else:
                badge_html = '<span style="background:#16a34a;color:#ffffff;font-size:10.5px;font-weight:800;padding:3px 9px;border-radius:99px;">🟢 พร้อมขาย (ถ้วย 5oz)</span>'

            qty_pill = (
                f'<span style="background:#d32f2f;color:#ffffff;font-size:11.5px;font-weight:800;padding:2px 9px;border-radius:99px;">เลือก {cur_qty} ถ้วย</span>'
                if (cur_qty > 0 and not is_oos)
                else ""
            )

            with f_cols[c_idx]:
                with st.container(border=True):
                    render_html(
                        f'<div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:6px;min-height:24px;">{badge_html}{qty_pill}</div>'
                    )
                    if thumb_str and Path(thumb_str).exists():
                        st.image(thumb_str, use_container_width=True)
                    else:
                        render_html(
                            '<div style="height:135px;background:#FFF8EE;border-radius:12px;display:flex;align-items:center;justify-content:center;font-size:38px;margin-bottom:6px;">🍨</div>'
                        )
                    title_color = "#94a3b8" if is_oos else ("#d32f2f" if cur_qty > 0 else "#2B1810")
                    render_html(
                        f'<div style="color:{title_color};font-weight:800;font-size:15px;line-height:1.35;min-height:36px;margin:6px 0 4px 0;">#{fid:02d}. {fname} <span style="font-size:11.5px;color:#64748b;font-weight:700;">(5 ออนซ์)</span></div>'
                    )
                    st.number_input(
                        f"จำนวนถ้วย #{fid:02d}",
                        min_value=0,
                        max_value=target_cups,
                        step=1,
                        key=f"qty_flv_{fid}",
                        disabled=is_oos,
                        label_visibility="collapsed",
                    )

    st.markdown("---")
    # ==========================================================================
    # 📲 ขั้นตอนที่ 3: กรอกชื่อ-ที่อยู่ผู้รับ + กล่องสรุปบิลอัตโนมัติ + ปุ่มส่งเข้า LINE & Facebook
    # ==========================================================================
    if current_selected_cups == target_cups:
        render_html(
            f'<div style="background:linear-gradient(135deg,#059669,#10b981);border:2.5px solid #fde047;border-radius:18px;padding:16px 20px;margin-top:6px;margin-bottom:12px;color:#ffffff;box-shadow:0 10px 26px rgba(5,150,105,0.22);"><div style="font-size:19px;font-weight:800;">✅ ขั้นตอนที่ 3: สรุปบิลสั่งซื้อไอศกรีมถ้วย 5 ออนซ์ (เลือกครบ {target_cups} ถ้วยตามโปรโมชันแล้ว!)</div><div style="font-size:13.8px;margin-top:4px;opacity:0.95;">กรอกชื่อผู้รับ เบอร์โทรศัพท์ และที่อยู่จัดส่งด้านล่าง แล้วกดปุ่มส่งบิลเข้า <b>LINE: Dayinterfood</b> หรือ <b>Facebook Page</b> ได้ทันทีครับ</div></div>'
        )
    else:
        render_html(
            f'<div style="background:linear-gradient(135deg,#d32f2f,#ff5252);border:2px solid #fde047;border-radius:18px;padding:16px 20px;margin-top:6px;margin-bottom:12px;color:#ffffff;box-shadow:0 8px 22px rgba(211,47,47,0.18);"><div style="font-size:18px;font-weight:800;">📝 ขั้นตอนที่ 3: กรอกชื่อ-ที่อยู่จัดส่ง & ตรวจสอบบิลสั่งซื้อ (ขณะนี้เลือกไว้ {current_selected_cups} / {target_cups} ถ้วย)</div><div style="font-size:13.5px;margin-top:4px;opacity:0.95;">💡 แนะนำให้จิ้มเลือกรสชาติด้านบนให้ครบ <b>{target_cups} ถ้วย</b> (หรือกดปุ่ม <b>⚡ จัดรสฮิตให้อัตโนมัติ</b>) ก่อนกดส่งบิลครับ</div></div>'
        )

    cust_col1, cust_col2 = st.columns(2)
    with cust_col1:
        cust_name = st.text_input(
            "👤 ชื่อผู้รับ (ชื่อ-นามสกุล ลูกค้า):",
            placeholder="เช่น คุณสมชาย ใจดี",
            key="mm_cust_name",
        )
        cust_phone = st.text_input(
            "📞 เบอร์โทรศัพท์ติดต่อ:",
            placeholder="เช่น 081-234-5678",
            key="mm_cust_phone",
        )
    with cust_col2:
        cust_address = st.text_area(
            "🏠 ที่อยู่จัดส่ง (บ้านเลขที่ หมู่บ้าน/ซอย ถนน ตำบล อำเภอ จังหวัด รหัสไปรษณีย์):",
            placeholder="กรอกที่อยู่จัดส่งให้ครบถ้วน เพื่อจัดส่งด้วยน้ำแข็งแห้งส่งตรงถึงหน้าบ้าน...",
            height=112,
            key="mm_cust_addr",
        )

    selected_lines = []
    selected_flavors_map = {}
    selected_short_items = []
    for f in flavors_list:
        q = int(st.session_state.get(f"qty_flv_{f['id']}", 0))
        if q > 0 and not f.get("out_of_stock"):
            selected_lines.append(f"  • #{f['id']:02d} {f['name']} = {q} ถ้วย")
            selected_flavors_map[str(f["id"])] = q
            selected_short_items.append(f"#{f['id']:02d} {f['name']} x{q}")

    flavors_block_str = (
        "\n".join(selected_lines)
        if selected_lines
        else "  • (ยังไม่ได้จิ้มเลือกรสชาติ — กรุณาเลือกรสชาติด้านบน)"
    )

    order_summary_text = (
        f"🍦 ใบสั่งซื้อเดย์ไอศครีม (DAY ICE CREAM ONLINE ORDER)\n"
        f"========================================\n"
        f"📦 โปรโมชันที่เลือก: {pkg_title}\n"
        f"🍨 จำนวนรวม: {current_selected_cups} / {target_cups} ถ้วย (ขนาด 5 ออนซ์)\n"
        f"💰 ยอดเงินรวมสุทธิ: {base_price:,} บาท ({pkg_note})\n"
        f"----------------------------------------\n"
        f"👤 ชื่อผู้รับ: {cust_name.strip() or '(รอระบุชื่อผู้รับ)'}\n"
        f"📞 เบอร์โทรศัพท์: {cust_phone.strip() or '(รอระบุเบอร์โทรศัพท์)'}\n"
        f"🏠 ที่อยู่จัดส่ง: {cust_address.strip() or '(รอระบุที่อยู่จัดส่ง)'}\n"
        f"----------------------------------------\n"
        f"📋 รายการรสชาติที่เลือก ({len(selected_lines)} รสชาติ รวม {current_selected_cups} ถ้วย):\n"
        f"{flavors_block_str}\n"
        f"========================================\n"
        f"👑 สมาชิก VIP เดย์ไอศกรีม | LINE ID: Dayinterfood | โทร: 086-3328091\n"
        f"🌐 เว็บแอป: app.dayicecream.com | เว็บหลัก: www.dayicecream.com"
    )

    # บันทึกข้อมูลสมาชิก VIP และออเดอร์ลงไฟล์ F:\DAY_ICECREAM_BRANCH_APP\vip_customers_ orders.csv อัตโนมัติทันทีที่กรอกข้อมูลครบ
    if current_selected_cups > 0 and (
        len(normalize_phone_digits(cust_phone)) >= 9
        or (cust_name.strip() and cust_address.strip())
    ):
        save_vip_customer_order(
            cust_name=cust_name,
            cust_phone=cust_phone,
            cust_address=cust_address,
            pkg_code=pkg_choice,
            pkg_title=pkg_title,
            total_cups=current_selected_cups,
            total_price=base_price,
            flavors_summary=" | ".join(selected_short_items),
            flavors_map=selected_flavors_map,
            full_bill_text=order_summary_text,
            force=False,
        )

    vip_save_col1, vip_save_col2 = st.columns([1.5, 2.5])
    with vip_save_col1:
        if st.button(
            "👑 บันทึกที่อยู่ & รสชาติโปรดไว้เป็นสมาชิก VIP ทันที",
            key="btn_manual_save_vip",
            use_container_width=True,
        ):
            ok_vip = save_vip_customer_order(
                cust_name=cust_name,
                cust_phone=cust_phone,
                cust_address=cust_address,
                pkg_code=pkg_choice,
                pkg_title=pkg_title,
                total_cups=current_selected_cups,
                total_price=base_price,
                flavors_summary=" | ".join(selected_short_items),
                flavors_map=selected_flavors_map,
                full_bill_text=order_summary_text,
                force=True,
            )
            if ok_vip:
                st.success(
                    "👑 บันทึกข้อมูลที่อยู่จัดส่งและรสชาติโปรดของคุณลงฐานข้อมูลสมาชิก VIP เรียบร้อยแล้ว!"
                )
    with vip_save_col2:
        render_html(
            '<div style="background:#fffbeb;border:1.5px solid #fde047;border-radius:12px;padding:10px 14px;color:#78350f;font-size:12.8px;font-weight:700;">👑 <b>ระบบ VIP Auto-Save:</b> เมื่อคุณกรอกชื่อ-เบอร์โทร-ที่อยู่และกดปุ่มสั่งซื้อ ระบบจะจดจำข้อมูลไว้ให้อัตโนมัติสำหรับการสั่งซื้อครั้งถัดไปทันที!</div>'
        )

    st.text_area(
        "📄 กล่องข้อความสรุปบิล (Order Summary Text — พร้อมส่งเข้าแชท LINE & Facebook หรือใช้พิมพ์บิลได้ทันที):",
        value=order_summary_text,
        height=255,
    )

    vip_js_payload = {
        "name": cust_name.strip(),
        "phone": cust_phone.strip(),
        "address": cust_address.strip(),
        "pkg": pkg_choice,
        "flavors": selected_flavors_map,
    }
    render_one_click_order_to_chat_buttons(
        order_text=order_summary_text,
        button_id_suffix="mixmatch",
        fb_page_url=fb_item.get("url") or "https://www.facebook.com/dayicecream",
        vip_payload=vip_js_payload,
    )


# ==============================================================================
# PAGE 3: 💰 3. สมัครแฟรนไชส์กำไร 100% (เครื่องคิดเลขคำนวณกำไร & คืนค่ามัดจำ 100%)
# ==============================================================================
elif current_page == "franchise":
    render_html(
        """
<div class="brand-section-header" style="background:linear-gradient(135deg,#b71c1c 0%,#d32f2f 55%,#f59e0b 100%);">
<div>
<div class="brand-section-title">💰 เครื่องคิดเลขคำนวณกำไรแฟรนไชส์อัจฉริยะ (Franchise Profit Simulator)</div>
<div class="brand-section-sub">ต้นทุนแฟรนไชส์เพียงถ้วยละ <b>25 บาท</b> (ราคาขายมาตรฐานเฉลี่ยทั่วประเทศ 40 บาท กำไร 15 บาท/ถ้วย) — ลองคำนวณกำไรต่อเดือนและต่อปีของร้านคุณได้ทันที!</div>
</div>
<div>
<span style="background:#fef08a;color:#991b1b;padding:7px 16px;border-radius:99px;font-size:13px;font-weight:800;box-shadow:0 4px 12px rgba(0,0,0,0.15);">🏆 เปิดแล้วกำไร 100% • คืนมัดจำ 100% ตลอด 10 ปี</span>
</div>
</div>
"""
    )

    FRANCHISE_COST_PER_CUP = 25

    sim_col_left, sim_col_right = st.columns([1.25, 1.35])

    with sim_col_left:
        render_html(
            '<div class="cream-card" style="border:2px solid #fca5a5;margin-bottom:12px;"><div style="color:#d32f2f;font-weight:800;font-size:17px;margin-bottom:4px;">🎯 ขั้นตอนที่ 1: เลือกราคาขายและยอดขายต่อเดือน</div><div style="color:#5C4033;font-size:13px;">ต้นทุนแฟรนไชส์คงที่ <b>25 บาท/ถ้วย</b> (ฟรี! ถ้วยกระดาษ ช้อน ช้อนชิม โคน และถั่วลิสงทุกรอบการสั่ง)</div></div>'
        )

        selling_price_options = {
            35: "35 บาท (กำไร 10 บาท/ถ้วย — เน้นออกไว ขายง่ายทุกทำเล)",
            40: "40 บาท (กำไร 15 บาท/ถ้วย — ⭐ ราคาขายมาตรฐานเฉลี่ยทั่วประเทศ)",
            45: "45 บาท (กำไร 20 บาท/ถ้วย — ร้านอาหาร / คาเฟ่ / แหล่งท่องเที่ยว)",
            50: "50 บาท (กำไร 25 บาท/ถ้วย — ร้านอาหารชั้นนำ / โซนพรีเมียม)",
            60: "60 บาท (กำไร 35 บาท/ถ้วย — โรงแรม / รีสอร์ต / ร้านระดับมิชลิน)",
        }
        selected_sell_price = st.radio(
            "💵 1. เลือกราคาขายต่อถ้วยที่คุณต้องการตั้งขาย:",
            options=[35, 40, 45, 50, 60],
            index=1,
            format_func=lambda x: selling_price_options[x],
            key="sim_sell_price",
        )

        monthly_cups_presets = {
            100: "100 ถ้วย/เดือน (รายได้เสริม)",
            150: "150 ถ้วย/เดือน (ขายได้เรื่อยๆ)",
            200: "200 ถ้วย/เดือน (มีลูกค้าประจำ)",
            300: "300 ถ้วย/เดือน (ขายดีมาก)",
            600: "600 ถ้วย/เดือน (ขายดีสุดๆ)",
        }

        if "sim_cups_value" not in st.session_state:
            st.session_state["sim_cups_value"] = 200

        def _on_preset_cups_change() -> None:
            st.session_state["sim_cups_value"] = int(st.session_state["sim_cups_radio"])

        selected_preset_cups = st.radio(
            "📈 2. คาดว่าขายได้เดือนละกี่ถ้วย? (คลิกเลือกเป้าหมายยอดขาย):",
            options=[100, 150, 200, 300, 600],
            index=2,
            format_func=lambda x: monthly_cups_presets[x],
            key="sim_cups_radio",
            on_change=_on_preset_cups_change,
        )

        custom_slider_cups = st.slider(
            "🎚️ หรือเลื่อนปรับจำนวนถ้วยต่อเดือนเอง (100 – 1,500 ถ้วย/เดือน):",
            min_value=100,
            max_value=1500,
            step=10,
            key="sim_cups_value",
        )

    profit_per_cup = int(selected_sell_price) - FRANCHISE_COST_PER_CUP
    monthly_cups = int(custom_slider_cups)
    avg_cups_per_day = monthly_cups / 30.0
    monthly_profit = profit_per_cup * monthly_cups
    yearly_profit_gross = monthly_profit * 12
    monthly_electric_cost = 500
    yearly_electric_cost = monthly_electric_cost * 12
    yearly_profit_net = yearly_profit_gross - yearly_electric_cost

    with sim_col_right:
        render_html(
            f"""
<div style="background:linear-gradient(145deg,#064e3b 0%,#047857 55%,#065f46 100%);border:3px solid #fbbf24;border-radius:22px;padding:20px 18px;color:#ffffff;box-shadow:0 14px 32px rgba(4,120,87,0.28);">
<div style="display:flex;justify-content:space-between;align-items:center;flex-wrap:wrap;gap:8px;margin-bottom:12px;">
<span style="background:#fef08a;color:#064e3b;font-weight:800;font-size:12.5px;padding:4px 12px;border-radius:99px;">🔥 ผลลัพธ์การคำนวณกำไรของคุณ</span>
<span style="font-size:13px;color:#d1fae5;font-weight:600;">ขายเฉลี่ยเพียงวันละ ~{avg_cups_per_day:.1f} ถ้วย ({monthly_cups:,} ถ้วย/เดือน)</span>
</div>
<div style="display:grid;grid-template-columns:1fr 1fr;gap:10px;margin-bottom:14px;">
<div style="background:rgba(255,255,255,0.12);border:1.5px solid rgba(254,240,138,0.5);border-radius:16px;padding:12px;">
<div style="font-size:12px;color:#fde68a;font-weight:700;">🍨 กำไรต่อถ้วย (ขาย {selected_sell_price}.- ทุน 25.-)</div>
<div style="font-size:24px;font-weight:800;color:#ffffff;margin-top:2px;">+{profit_per_cup:,} <span style="font-size:14px;">บาท/ถ้วย</span></div>
</div>
<div style="background:rgba(255,255,255,0.12);border:1.5px solid rgba(254,240,138,0.5);border-radius:16px;padding:12px;">
<div style="font-size:12px;color:#fde68a;font-weight:700;">💰 1) กำไรต่อเดือน ({monthly_cups:,} ถ้วย)</div>
<div style="font-size:24px;font-weight:800;color:#fef08a;margin-top:2px;">{monthly_profit:,} <span style="font-size:14px;">บาท/เดือน</span></div>
</div>
</div>
<div style="background:linear-gradient(135deg,#fef08a 0%,#fde047 50%,#facc15 100%);border:2.5px solid #ffffff;border-radius:18px;padding:14px 16px;text-align:center;color:#78350f;box-shadow:0 8px 22px rgba(0,0,0,0.22);margin-bottom:14px;">
<div style="font-size:14.5px;font-weight:800;color:#991b1b;">🎉 2) กำไรรวมต่อปี (12 เดือน = {monthly_cups * 12:,} ถ้วย/ปี)</div>
<div style="font-family:'Kanit','Prompt',sans-serif;font-size:34px;font-weight:900;color:#b91c1c;line-height:1.15;margin:4px 0;">{yearly_profit_gross:,} บาท/ปี</div>
<div style="font-size:12px;font-weight:700;color:#78350f;">(คิดจากกำไรเดือนละ {monthly_profit:,} บาท × 12 เดือน)</div>
</div>
<div style="background:rgba(0,0,0,0.26);border:1.5px solid #6ee7b7;border-radius:16px;padding:12px 14px;margin-bottom:12px;">
<div style="font-size:13px;color:#fde68a;font-weight:700;">⚡ 3) หักค่าไฟตู้แช่ประหยัดพลังงาน: ค่าไฟต่อเดือนไม่เกิน 500 บาท (12 เดือน = 6,000 บาท/ปี)</div>
<div style="display:flex;justify-content:space-between;align-items:center;flex-wrap:wrap;margin-top:8px;padding-top:8px;border-top:1px dashed rgba(255,255,255,0.3);">
<span style="font-size:14px;font-weight:800;color:#ffffff;">💎 กำไรสุทธิเข้ากระเป๋าต่อปี (หลังหักค่าไฟแล้ว):</span>
<span style="font-size:24px;font-weight:900;color:#4ade80;">{yearly_profit_net:,} บาท/ปี!</span>
</div>
</div>
<div style="background:linear-gradient(135deg,#b91c1c,#ef4444);border:2px solid #fef08a;border-radius:14px;padding:12px 14px;text-align:center;">
<div style="font-size:14.5px;font-weight:800;color:#ffffff;line-height:1.45;">🎁 แถมฟรีไอศกรีม 100 - 300 ถ้วย (แล้วแต่แพ็กเกจที่คุณลูกค้าเลือก)<br><span style="color:#fef08a;font-size:16px;">— สร้างกำไรรอบแรกคืนทุนทันที 5,000 - 10,000 บาท!</span></div>
</div>
</div>
"""
        )

    # --------------------------------------------------------------------------
    # 2) โซนใหม่ทันทีใต้ผลลัพธ์กำไร: 📦 เลือกรูปแบบแพ็กเกจแฟรนไชส์ที่ใช่สำหรับร้านคุณ & เปรียบเทียบความคุ้มค่า 100%
    # --------------------------------------------------------------------------
    render_html(
        """
<div class="brand-section-header" style="margin-top:20px;margin-bottom:14px;background:linear-gradient(135deg,#064e3b 0%,#047857 50%,#059669 100%);border:2.5px solid #fde047;">
<div>
<div class="brand-section-title" style="font-size:21px;">📦 เลือกรูปแบบแพ็กเกจแฟรนไชส์ที่ใช่สำหรับร้านคุณ & เปรียบเทียบความคุ้มค่า 100%</div>
<div class="brand-section-sub">🎁 แถมฟรีไอศกรีม 100 - 300 ถ้วย (แล้วแต่แพ็กเกจที่คุณลูกค้าเลือก) — สร้างกำไรรอบแรกคืนทุนทันที 5,000 - 10,000 บาท!</div>
</div>
<div>
<span style="background:#fef08a;color:#064e3b;padding:6px 14px;border-radius:99px;font-size:12.5px;font-weight:900;">💰 เลิกขายคืนเงินมัดจำ 100% เต็มจำนวน!</span>
</div>
</div>
"""
    )

    pkg_posters = [
        {
            "filename": "franchise_pkg_1.jpg",
            "fallback": APP_DIR / "ข้อดีแฟรนไชส์1.jpg",
            "badge": "🍦 แพ็กเกจที่ 1 & 2 • เลือกรูปแบบที่ใช่สำหรับร้านคุณ",
            "title": "เปรียบเทียบ 1. แบบถ้วยพร้อมทาน (12,500฿) vs 2. แบบตัก Scoop Style (25,000฿)",
            "subtitle": "🎁 แถมฟรีไอศกรีม 100 - 300 ถ้วย (แล้วแต่แพ็กเกจที่คุณลูกค้าเลือก) — สร้างกำไรรอบแรกคืนทุนทันที 5,000 - 10,000 บาท! • คืนเงินมัดจำ 100% เมื่อเลิกสัญญา",
        },
        {
            "filename": "franchise_pkg_2.jpg",
            "fallback": APP_DIR / "ข้อดีแฟรนไชส์.jpg",
            "badge": "💡 ความจริง: ตู้แช่ฟรี vs ตู้แช่แบบมัดจำ",
            "title": 'ความจริง: "ตู้แช่ฟรี" vs "ตู้แช่แบบมัดจำ Day Ice Cream" — ฟรี! ไอศกรีม 100 - 300 ถ้วย (แล้วแต่แพ็กเกจที่คุณลูกค้าเลือก)',
            "subtitle": "เหมือนเงินฝากธนาคาร เงินอยู่ครบปลอดภัย 100% • อิสระ 0 บาท ไม่มีขั้นต่ำรายเดือน • ฟรี! ไอศกรีม 100 - 300 ถ้วย (แล้วแต่แพ็กเกจที่คุณลูกค้าเลือก) สร้างกำไรรอบแรก 5,000 - 10,000 บาท!",
        },
    ]

    pkg_cols = st.columns(2)
    for p_idx, p_info in enumerate(pkg_posters):
        p_path = PROMO_GALLERY_DIR / p_info["filename"]
        if not p_path.exists() and p_info["fallback"].exists():
            p_path = p_info["fallback"]
        with pkg_cols[p_idx]:
            with st.container(border=True):
                render_html(
                    f'<div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:6px;"><span style="background:linear-gradient(135deg,#047857,#10b981);color:#ffffff;font-size:11.5px;font-weight:800;padding:4px 12px;border-radius:99px;">{p_info["badge"]}</span><span style="color:#065f46;font-size:12px;font-weight:800;">#PKG-0{p_idx+1}</span></div><div style="color:#b71c1c;font-weight:800;font-size:16px;line-height:1.35;min-height:42px;">{p_info["title"]}</div><div style="color:#5C4033;font-size:12.8px;line-height:1.45;margin-top:4px;margin-bottom:8px;">{p_info["subtitle"]}</div>'
                )
                if p_path.exists():
                    st.image(str(p_path), use_container_width=True)
                    if show_promo_zoom_dialog is not None:
                        if st.button(
                            f"🔍 คลิกขยายดูตารางเปรียบเทียบขนาดใหญ่คมชัด (#{p_idx+1})",
                            key=f"zoom_franchise_pkg_{p_idx+1}",
                            use_container_width=True,
                        ):
                            show_promo_zoom_dialog(
                                str(p_path),
                                p_info["title"],
                                p_info["subtitle"],
                                p_info["badge"],
                            )
                    else:
                        with st.expander(
                            f"🔍 คลิกขยายดูตารางเปรียบเทียบขนาดใหญ่คมชัด (#{p_idx+1})"
                        ):
                            st.image(
                                str(p_path),
                                caption=p_info["title"],
                                use_container_width=True,
                            )

    # --------------------------------------------------------------------------
    # 3) กล่อง 👑 การันตีไม่มีความเสี่ยงในการลงทุน 100% เจ้าเดียวในไทย! (พร้อมปุ่ม TikTok)
    # --------------------------------------------------------------------------
    render_html(
        """
<div style="background:linear-gradient(135deg,#fffbeb 0%,#fff1f2 55%,#fef3c7 100%);border:3px solid #d32f2f;border-radius:22px;padding:20px 18px;margin:20px 0;box-shadow:0 12px 30px rgba(211,47,47,0.14);">
<div style="display:flex;align-items:center;justify-content:space-between;flex-wrap:wrap;gap:12px;margin-bottom:14px;">
<div>
<span style="background:linear-gradient(135deg,#d32f2f,#b71c1c);color:#ffffff;font-weight:800;font-size:12.5px;padding:5px 14px;border-radius:99px;">🛡️ ZERO-RISK FRANCHISE GUARANTEE</span>
<h3 style="font-family:'Kanit','Prompt',sans-serif;color:#b71c1c;font-size:21px;font-weight:800;margin:8px 0 0 0;">👑 การันตีไม่มีความเสี่ยงในการลงทุน 100% เจ้าเดียวในไทย!</h3>
</div>
<a href="https://vt.tiktok.com/ZSg6HCD9N/" target="_blank" rel="noopener noreferrer" style="background:linear-gradient(135deg,#111827 0%,#be123c 55%,#ec4899 100%);color:#ffffff;font-weight:800;font-size:14px;padding:12px 18px;border-radius:14px;text-decoration:none;border:2px solid #f9a8d4;box-shadow:0 8px 22px rgba(236,72,153,0.35);display:inline-flex;align-items:center;gap:8px;">📱 คลิกชมวิดีโอ: ตัวอย่างการรับประกันคืนร้าน คืนเงินมัดจำให้ 100% บน TikTok ↗</a>
</div>
<div style="display:grid;grid-template-columns:repeat(auto-fit,minmax(260px,1fr));gap:10px;">
<div style="background:#FFFFFF;border-left:5px solid #d32f2f;border-radius:12px;padding:12px 14px;box-shadow:0 4px 12px rgba(0,0,0,0.05);color:#2B1810;font-weight:700;font-size:13.8px;line-height:1.5;">✔️ <b>ด้วยระบบคุ้มครองการลงทุน คืนเงินมัดจำตู้และอุปกรณ์ให้ 100%</b></div>
<div style="background:#FFFFFF;border-left:5px solid #d97706;border-radius:12px;padding:12px 14px;box-shadow:0 4px 12px rgba(0,0,0,0.05);color:#2B1810;font-weight:700;font-size:13.8px;line-height:1.5;">✔️ <b>ตลอดอายุสัญญา 10 ปี เจ้าเดียวในไทย</b> (คืนเงินให้ 100% ตลอดอายุสัญญา — เราเป็นแฟรนไชส์เดียวที่ซื้อตู้ไอศกรีมคืนจากลูกค้า 100%)</div>
<div style="background:#FFFFFF;border-left:5px solid #059669;border-radius:12px;padding:12px 14px;box-shadow:0 4px 12px rgba(0,0,0,0.05);color:#2B1810;font-weight:700;font-size:13.8px;line-height:1.5;">✔️ <b>ทางบริษัทดูแลตู้ + เปลี่ยนอุปกรณ์ขายให้ใหม่ฟรี!</b> ตลอดอายุสัญญา 10 ปี ไม่มีทางขาดทุน เจ้าเดียวในประเทศไทย</div>
<div style="background:#FFFFFF;border-left:5px solid #e11d48;border-radius:12px;padding:12px 14px;box-shadow:0 4px 12px rgba(0,0,0,0.05);color:#2B1810;font-weight:700;font-size:13.8px;line-height:1.5;">✔️ <b>🎁 แถมฟรีไอศกรีม 100 - 300 ถ้วย (แล้วแต่แพ็กเกจที่คุณลูกค้าเลือก) — สร้างกำไรรอบแรกคืนทุนทันที 5,000 - 10,000 บาท!</b> (เลิกขายเมื่อไหร่ก็ได้ค่ามัดจำคืน 100%)</div>
</div>
</div>
"""
    )

    # --------------------------------------------------------------------------
    # 4) แสดงชุดภาพหลักฐานความสำเร็จและมาตรฐาน Michelin Guide 4 ภาพหลัก (ป้ายโฆษณา 001.jpg ถึง 004.jpg)
    # --------------------------------------------------------------------------
    render_html(
        """
<div style="background:linear-gradient(135deg,#fffDF9 0%,#fff1f2 100%);border:2.5px solid #fca5a5;border-radius:20px;padding:16px;margin:14px 0 12px 0;display:flex;align-items:center;justify-content:space-between;flex-wrap:wrap;gap:10px;">
<div>
<span style="background:linear-gradient(135deg,#d32f2f,#ff5252);color:#ffffff;font-weight:800;font-size:12px;padding:4px 12px;border-radius:99px;">🏆 หลักฐานความสำเร็จ & มาตรฐานระดับโลก</span>
<div style="font-family:'Kanit','Prompt',sans-serif;font-size:20px;font-weight:800;color:#b71c1c;margin-top:4px;">👑 มาตรฐานร้าน Michelin Guide 10+ สาขา • ประโยชน์แฟรนไชส์ 6 ข้อ • เมนูโฮมเมด 30 รสชาติ</div>
</div>
<span style="color:#78350f;font-size:12.5px;font-weight:700;">🔍 กดที่ปุ่มใต้ภาพเพื่อขยายดูรายละเอียดขนาดใหญ่</span>
</div>
"""
    )

    franchise_4_posters = [
        {
            "filename": "ป้ายโฆษณา 001.jpg",
            "badge": "🥥 ภาพที่ 1 • ความสุขที่คุณสัมผัสได้",
            "title": "ความสุขที่คุณสัมผัสได้ (ไอศกรีมรวมมิตร กะทิทับสะแกคั้นสด & มะพร้าวน้ำหอมบ้านแพ้ว 100%)",
            "subtitle": "คัดสรรสุดยอดวัตถุดิบไทยแท้ กะทิทับสะแกคั้นสดและน้ำมะพร้าวน้ำหอมบ้านแพ้ว 100% หอมมันเข้มข้น ไร้สารเคมี",
        },
        {
            "filename": "ป้ายโฆษณา 002.jpg",
            "badge": "🏆 ภาพที่ 2 • มาตรฐานร้านมิชลิน 10+ สาขา",
            "title": "มาตรฐานระดับโลก ที่ร้าน Michelin Guide & Bib Gourmand กว่า 10 สาขาไว้วางใจ",
            "subtitle": "การันตีคุณภาพด้วยร้านอาหารระดับมิชลินไกด์กว่า 10 สาขา และร้านอาหารชั้นนำทั่วประเทศกว่า 200 สาขาเลือกเสิร์ฟ",
        },
        {
            "filename": "ป้ายโฆษณา 003.jpg",
            "badge": "🛡️ ภาพที่ 3 • ประโยชน์แฟรนไชส์ 6 ข้อ",
            "title": "ประโยชน์ของการเปิดแฟรนไชส์ Day Ice Cream 6 ข้อ (เปิดแล้วกำไร 100% คืนค่ามัดจำตู้ 100%)",
            "subtitle": "🎁 แถมฟรีไอศกรีม 100 - 300 ถ้วย (แล้วแต่แพ็กเกจที่คุณลูกค้าเลือก) — สร้างกำไรรอบแรกคืนทุนทันที 5,000 - 10,000 บาท! เลิกขายคืนเงินมัดจำ 100% ตลอดสัญญา 10 ปี",
        },
        {
            "filename": "ป้ายโฆษณา 004.jpg",
            "badge": "🍨 ภาพที่ 4 • โปสเตอร์เมนูไอศกรีมโฮมเมด",
            "title": "ป้ายเมนูไอศกรีมโฮมเมดพรีเมียม 100% Organic (ครบทุกรสชาติซิกเนเจอร์ขายดี)",
            "subtitle": "รวมรสชาติยอดนิยมจากกะทิคั้นสด นมโคสดแท้นิวซีแลนด์ และผลไม้สดแท้ตามฤดูกาล ปราศจากสารเสริมคุณภาพ",
        },
    ]

    for row_idx in range(0, 4, 2):
        f4_cols = st.columns(2)
        for c_idx in range(2):
            p4_idx = row_idx + c_idx
            p4 = franchise_4_posters[p4_idx]
            p4_path = PROMO_GALLERY_DIR / p4["filename"]
            with f4_cols[c_idx]:
                with st.container(border=True):
                    render_html(
                        f'<div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:6px;"><span style="background:linear-gradient(135deg,#d32f2f,#ff5252);color:#ffffff;font-size:11.5px;font-weight:800;padding:4px 11px;border-radius:99px;">{p4["badge"]}</span><span style="color:#8d6e63;font-size:12px;font-weight:800;">#0{p4_idx+1}/04</span></div><div style="color:#b71c1c;font-weight:800;font-size:16px;line-height:1.35;min-height:42px;">{p4["title"]}</div><div style="color:#5C4033;font-size:12.8px;line-height:1.45;margin-top:4px;margin-bottom:8px;">{p4["subtitle"]}</div>'
                    )
                    if p4_path.exists():
                        st.image(str(p4_path), use_container_width=True)
                        if show_promo_zoom_dialog is not None:
                            if st.button(
                                f"🔍 คลิกขยายดูภาพใหญ่คมชัด (#0{p4_idx+1})",
                                key=f"zoom_fr4_{p4_idx+1}_{p4['filename']}",
                                use_container_width=True,
                            ):
                                show_promo_zoom_dialog(
                                    str(p4_path),
                                    p4["title"],
                                    p4["subtitle"],
                                    p4["badge"],
                                )
                        else:
                            with st.expander(f"🔍 คลิกขยายดูภาพใหญ่คมชัด (#0{p4_idx+1})"):
                                st.image(
                                    str(p4_path),
                                    caption=p4["title"],
                                    use_container_width=True,
                                )

    # --------------------------------------------------------------------------
    # 5) ปิดท้ายด้วย 3 หมวดความอร่อยพรีเมียม, 7 ข้อการันตีความสำเร็จ, ปุ่มทัก LINE และดีลเลอร์ประจำจังหวัด
    # --------------------------------------------------------------------------
    render_html(
        """
<div class="brand-section-header">
<div>
<div class="brand-section-title">🏭 มาตรฐานโรงงานเดย์ไอศครีม: 3 หมวดความอร่อยพรีเมียม & 7 สิทธิประโยชน์เหนือระดับ</div>
<div class="brand-section-sub">คัดสรรวัตถุดิบธรรมชาติแท้ 100% ไร้สารเสริมคุณภาพ อิมัลซิไฟเออร์ และสารกันบูด — มาตรฐานระดับเดียวกับไอศกรีมที่ดีที่สุดในโลก</div>
</div>
</div>
<div style="display:grid;grid-template-columns:repeat(auto-fit,minmax(260px,1fr));gap:14px;margin-bottom:18px;">
<div class="cream-card" style="border-top:5px solid #16a34a;">
<div style="font-size:26px;margin-bottom:4px;">🥥</div>
<div style="color:#15803d;font-weight:800;font-size:17px;margin-bottom:4px;">1. ไอศครีมกะทิ (100% Fresh Coconut)</div>
<div style="color:#4A2C2A;font-size:13.5px;line-height:1.5;">ผลิตจาก <b>น้ำมะพร้าวน้ำหอม 100% + กะทิคั้นสด</b> ไม่ใส่หางกะทิ หรือน้ำเปล่าแต่อย่างใด หอมมันหวานธรรมชาติแท้ทุกคำ</div>
</div>
<div class="cream-card" style="border-top:5px solid #0284c7;">
<div style="font-size:26px;margin-bottom:4px;">🥛</div>
<div style="color:#0369a1;font-weight:800;font-size:17px;margin-bottom:4px;">2. ไอศครีมนมสด (New Zealand Cream)</div>
<div style="color:#4A2C2A;font-size:13.5px;line-height:1.5;">ผลิตจาก <b>นมโคสดแท้ 100% & ครีมแท้นิวซีแลนด์</b> เนื้อเนียนแน่น หอมละมุน ไม่ใช้นมผงและไม่ใช้น้ำมันพืช</div>
</div>
<div class="cream-card" style="border-top:5px solid #e11d48;">
<div style="font-size:26px;margin-bottom:4px;">🍓</div>
<div style="color:#be123c;font-weight:800;font-size:17px;margin-bottom:4px;">3. ไอศครีมผลไม้สด (100% Fresh Fruit)</div>
<div style="color:#4A2C2A;font-size:13.5px;line-height:1.5;">ผลิตจาก <b>ผลไม้สด 100% ไม่ใช้ผลไม้แช่แข็ง</b> คัดผลไม้สดตามฤดูกาลเพื่อให้ได้รสชาติเปรี้ยวอมหวานสดชื่นแท้จริง</div>
</div>
</div>
<div style="background:#FFFFFF;border:2px solid #fca5a5;border-radius:22px;padding:20px 18px;margin-bottom:20px;box-shadow:0 10px 28px rgba(211,47,47,0.09);">
<div style="color:#b71c1c;font-family:'Kanit','Prompt',sans-serif;font-size:20px;font-weight:800;margin-bottom:12px;">🌟 สิ่งที่คุณลูกค้าจะได้รับจาก เดย์ไอศครีม (7 ข้อการันตีความสำเร็จ)</div>
<div style="display:grid;grid-template-columns:1fr;gap:10px;">
<div style="background:#FFFBF5;border:1.5px solid #f3dfd3;border-radius:14px;padding:12px 14px;"><span style="background:#d32f2f;color:#fff;font-weight:800;font-size:12px;padding:3px 10px;border-radius:99px;margin-right:8px;">ข้อที่ 1</span><b style="color:#2B1810;font-size:14.5px;">ไม่มีความเสี่ยงในการลงทุน</b></div>
<div style="background:#FFFBF5;border:1.5px solid #f3dfd3;border-radius:14px;padding:12px 14px;"><span style="background:#d32f2f;color:#fff;font-weight:800;font-size:12px;padding:3px 10px;border-radius:99px;margin-right:8px;">ข้อที่ 2</span><b style="color:#2B1810;font-size:14.5px;">ไม่ต้องซื้อแฟรนไชส์ เพียงแค่ยืมของกัน</b></div>
<div style="background:#FFFBF5;border:1.5px solid #fde68a;border-radius:14px;padding:12px 14px;"><span style="background:#d97706;color:#fff;font-weight:800;font-size:12px;padding:3px 10px;border-radius:99px;margin-right:8px;">ข้อที่ 3</span><b style="color:#2B1810;font-size:14.5px;">เลิกขายได้เงินมัดจำคืนเต็มจำนวน คุ้มครองยาวนาน 10 ปี</b><span style="color:#4A2C2A;font-size:14px;"> พร้อม <b style="color:#d32f2f;">🎁 แถมฟรีไอศกรีม 100 - 300 ถ้วย (แล้วแต่แพ็กเกจที่คุณลูกค้าเลือก) — สร้างกำไรรอบแรกคืนทุนทันที 5,000 - 10,000 บาท!</b> <b>^__^</b></span></div>
<div style="background:#FFFBF5;border:1.5px solid #f3dfd3;border-radius:14px;padding:12px 14px;"><span style="background:#d32f2f;color:#fff;font-weight:800;font-size:12px;padding:3px 10px;border-radius:99px;margin-right:8px;">ข้อที่ 4</span><b style="color:#2B1810;font-size:14.5px;">สร้างผลกำไรได้ง่าย</b><span style="color:#4A2C2A;font-size:14px;"> ด้วยสินค้าที่เป็นเอกลักษณ์ ไม่มีคู่แข่ง</span></div>
<div style="background:#FFFBF5;border:1.5px solid #f3dfd3;border-radius:14px;padding:12px 14px;"><span style="background:#d32f2f;color:#fff;font-weight:800;font-size:12px;padding:3px 10px;border-radius:99px;margin-right:8px;">ข้อที่ 5</span><b style="color:#2B1810;font-size:14.5px;">สร้างความประทับใจให้ลูกค้าในร้านของคุณ</b><span style="color:#4A2C2A;font-size:14px;"> ให้มาซื้อซ้ำและกลับมาใช้บริการใหม่ ด้วยเมนูของหวานจากไอศกรีมสุดอร่อย</span></div>
<div style="background:linear-gradient(135deg,#fffbeb,#fff1f2);border:2px solid #f59e0b;border-radius:14px;padding:14px 16px;"><span style="background:#b91c1c;color:#fff;font-weight:800;font-size:12px;padding:3px 10px;border-radius:99px;margin-right:8px;">ข้อที่ 6 ⭐ ไฮไลต์ระดับโลก</span><b style="color:#b71c1c;font-size:15px;">ได้รับไอศกรีมโฮมเมด "ที่ดีที่สุด"</b><span style="color:#2B1810;font-size:14px;line-height:1.55;"> ที่ผลิตจากผลไม้แท้ 100%, นมโคสดแท้ & ครีมสดนิวซีแลนด์, มะพร้าวน้ำหอมกะทิสด <b style="color:#d32f2f;">ไม่มีนมผง, ไม่มีแป้ง, ไม่มีผงไอศกรีม, ไม่มียากันบูด และไม่มีอิมัลซิไฟเออร์ใดๆ เจ้าเดียวในประเทศไทย</b><br><span style="color:#78350f;font-size:13.2px;font-style:italic;">🏆 (ไอศกรีมที่ไม่มีสารเสริมบนโลกนี้ มียี่ห้อเดียวคือ <b>Häagen-Dazs ฮาเกนดาส</b> ซึ่งได้รับรางวัลเป็นไอศกรีมที่ดีที่สุดในโลก ซึ่งเราต้องการที่จะเป็นไอศกรีมที่ดีที่สุดในโลกเช่นกัน!)</span></span></div>
<div style="background:#FFFBF5;border:1.5px solid #bbf7d0;border-radius:14px;padding:12px 14px;"><span style="background:#16a34a;color:#fff;font-weight:800;font-size:12px;padding:3px 10px;border-radius:99px;margin-right:8px;">ข้อที่ 7</span><b style="color:#15803d;font-size:14.5px;">เรามุ่งมั่นที่จะทำไอศกรีมที่อร่อยที่สุดในประเทศไทย</b><span style="color:#4A2C2A;font-size:14px;"> เพื่อให้คุณลูกค้าทุกท่านมีความสุขในการกินไอศครีมให้มากที่สุด</span></div>
</div>
<div style="display:flex;gap:12px;flex-wrap:wrap;margin-top:16px;">
<a href="https://line.me/ti/p/BX7Fscqs71" target="_blank" rel="noopener noreferrer" style="flex:2;min-width:250px;text-align:center;background:linear-gradient(135deg,#059669,#10b981);color:#ffffff;font-weight:800;font-size:15.5px;padding:14px 18px;border-radius:16px;text-decoration:none;box-shadow:0 8px 22px rgba(16,185,129,0.3);">💬 สนใจเปิดร้านแฟรนไชส์ (รับกำไรฟรีรอบแรก 5,000-10,000 บาท) ทัก LINE: Dayinterfood</a>
<a href="tel:0863328091" target="_blank" style="flex:1;min-width:200px;text-align:center;background:linear-gradient(135deg,#d32f2f,#ff5252);color:#ffffff;font-weight:800;font-size:15.5px;padding:14px 18px;border-radius:16px;text-decoration:none;box-shadow:0 8px 22px rgba(211,47,47,0.28);">📞 โทรปรึกษาคุณเดย์: 086-3328091</a>
</div>
</div>
"""
    )

    # ศูนย์ตัวแทนดีลเลอร์เดย์ไอศครีมประจำจังหวัด
    render_html(
        '<div class="brand-section-header"><div><div class="brand-section-title">📍 ศูนย์ตัวแทนดีลเลอร์เดย์ไอศครีมประจำจังหวัด</div><div class="brand-section-sub">สำหรับร้านค้า ร้านอาหาร คาเฟ่ และลูกค้าในพื้นที่ที่ต้องการลงตู้เดย์ไอศครีม หรือสั่งซื้อสินค้าผ่านตัวแทนประจำจังหวัดโดยตรง</div></div></div>'
    )

    dealers_info = [
        {
            "region": "🏯 ดีลเลอร์ จ.บุรีรัมย์ & จ.สุรินทร์",
            "contact": "คุณกานท์ณัฏฐา กนกวุฒิรักษ์พร (คุณผึ้ง) & พี่โหน่ง",
            "phone": "081-689-1648",
            "tel_href": "tel:0816891648",
            "address": "67 ถ.นิวาศน์ ต.ในเมือง อ.เมือง จ.บุรีรัมย์ 31000",
            "detail": "ตัวแทนดีลเลอร์ดูแลพื้นที่ จ.บุรีรัมย์ และ จ.สุรินทร์ (ฟรีค่าลงตู้สำหรับร้านอาหารในพื้นที่)",
            "link_url": "https://www.facebook.com/dayicecreamburiramsurin/",
            "link_label": "💬 ทักแชทเพจ DayIcecream บุรีรัมย์ ❯",
        },
        {
            "region": "⛰️ ดีลเลอร์ จ.เชียงใหม่ (ภาคเหนือ)",
            "contact": "คุณโชติพัฒน์ & คุณวีระกิตติ์ (ทีมงาน Day Ice Cream เชียงใหม่)",
            "phone": "099-615-3654, 097-965-5647",
            "tel_href": "tel:0996153654",
            "address": "ศูนย์กระจายสินค้า เดย์ไอศกรีม จังหวัดเชียงใหม่ (LINE: @daycnx6249)",
            "detail": "ดูแลร้านอาหาร คาเฟ่ และจุดจำหน่ายทั่วจังหวัดเชียงใหม่และพื้นที่ใกล้เคียง",
            "link_url": "https://www.facebook.com/daycnx6249",
            "link_label": "💬 ทักแชทเพจ Day Ice Cream เชียงใหม่ ❯",
        },
        {
            "region": "🏖️ ดีลเลอร์ จ.พังงา (ตะกั่วป่า / เขาหลัก)",
            "contact": "พี่ป้อม (ดีลเลอร์ประจำจังหวัดพังงา)",
            "phone": "098-786-0792",
            "tel_href": "tel:0987860792",
            "extra_tel_btn": True,
            "address": "ร้านก๋วยเตี๋ยวเรือหม้อดิน อ.ตะกั่วป่า จ.พังงา",
            "detail": "ดูแลจุดจำหน่ายและบริการลงตู้เดย์ไอศกรีมสำหรับร้านอาหารและคาเฟ่ทั่วจังหวัดพังงา",
            "link_url": "https://www.facebook.com/dayicecream",
            "link_label": "💬 ทักเพจ Day Ice Cream (ติดต่อสาขาพังงา) ❯",
        },
        {
            "region": "🌊 ดีลเลอร์ จ.ภูเก็ต",
            "contact": "คุณมด (ดีลเลอร์ประจำจังหวัดภูเก็ต)",
            "phone": "081-787-8133",
            "tel_href": "tel:0817878133",
            "address": "ร้านถนนกระบี่ Drinks & Homemade Ice Cream อ.เมือง จ.ภูเก็ต",
            "detail": "ดูแลจุดจำหน่ายทั้งแบบตักและแบบถ้วยสำเร็จรูป 5 ออนซ์ ทั่วเกาะภูเก็ต",
            "link_url": "https://www.facebook.com/profile.php?id=100063900291809",
            "link_label": "📘 เปิดเพจดีลเลอร์ จ.ภูเก็ต ❯",
        },
    ]

    cards_html_parts = ['<div class="dealer-cards-grid">']
    for dl in dealers_info:
        extra_call_html = (
            f'<a href="{dl["tel_href"]}" style="display:block;text-align:center;background:#fff1f2;color:#b91c1c;border:1.5px solid #fecdd3;font-weight:800;font-size:12px;padding:6px 10px;border-radius:9px;text-decoration:none;margin-bottom:7px;white-space:nowrap;">📞 กดโทรด่วนหาพี่ป้อม: {dl["phone"]}</a>'
            if dl.get("extra_tel_btn")
            else ""
        )
        cards_html_parts.append(
            f'<div class="dealer-card" style="display:flex;flex-direction:column;justify-content:space-between;height:100%;">'
            f'<div>'
            f'<div style="color:#d32f2f;font-weight:800;font-size:15.5px;margin-bottom:6px;">{dl["region"]}</div>'
            f'<div style="color:#2B1810;font-weight:700;font-size:13.5px;margin-bottom:5px;">👤 {dl["contact"]}</div>'
            f'<div style="margin-bottom:6px;"><a href="{dl["tel_href"]}" style="color:#b71c1c;font-weight:800;font-size:14px;text-decoration:none;">📞 โทร: {dl["phone"]}</a></div>'
            f'<div style="color:#4A2C2A;font-size:12.5px;line-height:1.45;margin-bottom:6px;">📍 {dl["address"]}</div>'
            f'<div style="color:#5C4033;font-size:12px;line-height:1.4;margin-bottom:12px;">{dl["detail"]}</div>'
            f'</div>'
            f'<div style="margin-top:auto;">'
            f'{extra_call_html}'
            f'<a href="{dl["link_url"]}" target="_blank" rel="noopener noreferrer" style="display:block;text-align:center;background:linear-gradient(135deg,#d32f2f,#ff5252);color:#fff;font-weight:700;font-size:12.2px;padding:9px 8px;border-radius:10px;text-decoration:none;box-shadow:0 4px 12px rgba(211,47,47,0.2);white-space:nowrap;overflow:hidden;text-overflow:ellipsis;">{dl["link_label"]}</a>'
            f'</div>'
            f'</div>'
        )
    cards_html_parts.append("</div>")
    render_html("".join(cards_html_parts))


# ==============================================================================
# PAGE 4: 🎉 4. จองไอศกรีมจัดเลี้ยงนอกสถานที่ (150 - 200+ ถ้วย)
# ==============================================================================
elif current_page == "catering":
    render_html(
        """
<div class="brand-section-header">
<div>
<div class="brand-section-title">🎉 คำนวณและจองไอศกรีมจัดเลี้ยง (เขตกรุงเทพฯ และปริมณฑล)</div>
<div class="brand-section-sub">บริการจัดส่งไอศกรีมสำหรับ งานวันเกิด • งานบุญ/งานบวช • งานแต่งงาน • งานเลี้ยงบริษัท • งานสัมมนาและอีเวนต์ทุกประเภท (เริ่มต้นที่ 150 ถ้วยขึ้นไป)</div>
</div>
<div>
<span style="background:#ffffff;color:#d32f2f;padding:6px 14px;border-radius:99px;font-size:12.5px;font-weight:800;">🎁 200 ถ้วยขึ้นไป ฟรีค่าส่ง + ยืมตู้ฟรี!</span>
</div>
</div>
"""
    )

    cat_col1, cat_col2, cat_col3 = st.columns([1.2, 1.3, 1.5])
    with cat_col1:
        event_type = st.selectbox(
            "🎈 ประเภทงานจัดเลี้ยง:",
            [
                "🎂 งานวันเกิด / ปาร์ตี้ครอบครัว",
                "🙏 งานบุญ / งานบวช / โรงทาน",
                "💍 งานมงคลสมรส (งานแต่งงาน)",
                "🏢 งานเลี้ยงบริษัท / สัมมนา / ประชุม",
                "🎪 งานอีเวนต์ / ออกบูธ / อื่นๆ",
            ],
        )
        serving_style = st.radio(
            "🍨 เลือกรูปแบบไอศกรีมจัดเลี้ยง:",
            [
                "แบบถ้วยบรรจุสำเร็จ 5 ออนซ์ (พร้อมฝาและช้อน แจกง่าย สะดวก รวดเร็ว)",
                "แบบถังตัก (สำหรับตักเสิร์ฟสดในงานเลี้ยง)",
            ],
        )

    with cat_col2:
        catering_cups = st.number_input(
            "🔢 เลือกจำนวนถ้วยสำหรับงานเลี้ยง (เริ่มต้นที่ 150 ถ้วยขึ้นไป):",
            min_value=150,
            max_value=5000,
            value=200,
            step=10,
        )
        event_date = st.date_input(
            "📅 วันที่จัดงานเลี้ยง:",
            value=datetime.date.today() + datetime.timedelta(days=3),
        )

    with cat_col3:
        icecream_cost = int(catering_cups) * 30
        if catering_cups < 200:
            shipping_fee = 400
            bonus_choice = "ค่าจัดส่ง 400 บาท (เขตกรุงเทพฯ และปริมณฑล)"
            render_html(
                f'<div style="background:#FFF8EE;border:2px solid #f59e0b;border-radius:16px;padding:14px;margin-bottom:8px;"><div style="color:#b45309;font-weight:800;font-size:15px;">🚚 เงื่อนไขการจัดส่ง (150 – 199 ถ้วย)</div><div style="color:#4A2C2A;font-size:13.5px;margin-top:4px;">• ค่าจัดส่ง <b>400 บาท</b> (สำหรับเขตกรุงเทพฯ และปริมณฑล)<br>💡 <i>เพิ่มอีกเพียง <b>{200 - catering_cups} ถ้วย</b> (ครบ 200 ถ้วย) รับสิทธิ์ <b>ฟรีค่าจัดส่ง + ฟรีกล่องโฟม + ฟรีน้ำแข็งแห้ง หรือยืมตู้ไอศกรีมฟรี!</b></i></div></div>'
            )
        else:
            shipping_fee = 0
            render_html(
                '<div style="background:linear-gradient(135deg,#059669,#10b981);border-radius:16px;padding:14px 16px;margin-bottom:8px;color:#ffffff;box-shadow:0 6px 18px rgba(16,185,129,0.25);"><div style="font-weight:800;font-size:15px;">🎁 สิทธิพิเศษ 200 ถ้วยขึ้นไป: ฟรีค่าจัดส่ง + ฟรีกล่องโฟม + ฟรีน้ำแข็งแห้ง (หรือเลือกรับสิทธิ์ ยืมตู้ไอศกรีมฟรี!)</div></div>'
            )
            bonus_choice = st.radio(
                "🎁 เลือกรับสิทธิพิเศษสำหรับ 200 ถ้วยขึ้นไป:",
                [
                    "🧊 รับฟรี! ค่าจัดส่ง + ฟรีกล่องโฟมเก็บความเย็น + ฟรีน้ำแข็งแห้ง",
                    "❄️ รับฟรี! ค่าจัดส่ง + สิทธิ์ยืมตู้แช่ไอศกรีมตั้งในงานฟรี!",
                ],
            )

        total_catering_price = icecream_cost + shipping_fee
        render_html(
            f'<div style="background:linear-gradient(135deg,#d32f2f,#ff5252);border-radius:14px;padding:10px 16px;display:flex;justify-content:space-between;align-items:center;color:#ffffff;"><span style="font-size:14px;font-weight:700;">💰 ประมาณการยอดรวม ({catering_cups} ถ้วย):</span><span style="font-size:19px;font-weight:800;">{total_catering_price:,} บาท</span></div>'
        )

    avail_flavor_names = [
        f"#{f['id']:02d} {f['name']}" for f in flavors_list if not f.get("out_of_stock")
    ]
    selected_catering_flavors = st.multiselect(
        "🍨 เลือกรสชาติที่ต้องการใช้ในงานจัดเลี้ยง (เลือกได้หลายรสชาติ):",
        options=avail_flavor_names,
        default=avail_flavor_names[:5]
        if len(avail_flavor_names) >= 5
        else avail_flavor_names,
    )

    ev_col1, ev_col2 = st.columns(2)
    with ev_col1:
        ev_contact_name = st.text_input(
            "👤 ชื่อผู้ติดต่อจองงานเลี้ยง:",
            placeholder="เช่น คุณกานดา (ฝ่ายจัดเลี้ยง)",
            key="cat_name",
        )
        ev_contact_phone = st.text_input(
            "📞 เบอร์โทรศัพท์ผู้ติดต่อ:",
            placeholder="เช่น 089-999-8888",
            key="cat_phone",
        )
    with ev_col2:
        ev_location = st.text_area(
            "📍 สถานที่จัดงานเลี้ยง (ชื่อหมู่บ้าน/วัด/โรงแรม/บริษัท แขวง/เขต จังหวัด และเวลาเริ่มงาน):",
            placeholder="ระบุสถานที่จัดงานในเขตกรุงเทพฯ/ปริมณฑล และเวลาที่ต้องการให้ส่งถึงหน้างาน...",
            height=108,
            key="cat_loc",
        )

    catering_summary_text = (
        f"🎉 ใบจองไอศกรีมจัดเลี้ยง (DAY ICE CREAM CATERING BOOKING)\n"
        f"========================================\n"
        f"🎈 ประเภทงาน: {event_type}\n"
        f"🍨 รูปแบบการเสิร์ฟ: {serving_style}\n"
        f"🔢 จำนวนที่สั่ง: {catering_cups} ถ้วย\n"
        f"🎁 สิทธิพิเศษ/การจัดส่ง: {bonus_choice}\n"
        f"💰 ประมาณการยอดรวม: {total_catering_price:,} บาท (ค่าไอศกรีม {icecream_cost:,}.- + ค่าส่ง {shipping_fee}.-)\n"
        f"----------------------------------------\n"
        f"📅 วันที่จัดงาน: {event_date.strftime('%d/%m/%Y')}\n"
        f"👤 ชื่อผู้ติดต่อ: {ev_contact_name.strip() or '(รอระบุชื่อผู้ติดต่อ)'}\n"
        f"📞 เบอร์โทร: {ev_contact_phone.strip() or '(รอระบุเบอร์โทร)'}\n"
        f"📍 สถานที่จัดงาน: {ev_location.strip() or '(รอระบุสถานที่จัดงาน)'}\n"
        f"----------------------------------------\n"
        f"🍨 รสชาติที่เลือกสำหรับงานเลี้ยง ({len(selected_catering_flavors)} รสชาติ):\n"
        + (
            "\n".join(f"  • {fn}" for fn in selected_catering_flavors)
            if selected_catering_flavors
            else "  • (รอเลือกรสชาติ)"
        )
        + "\n========================================\n"
        f"💬 ส่งใบจองที่ LINE ID: Dayinterfood | โทร: 086-3328091"
    )

    st.text_area(
        "📄 สรุปใบจองไอศกรีมจัดเลี้ยง (พร้อมคัดลอกส่งเข้า LINE: Dayinterfood):",
        value=catering_summary_text,
        height=220,
    )
    render_copy_and_line_buttons(catering_summary_text, "catering")


# ==============================================================================
# PAGE 5: 🏆 5. มาตรฐาน Michelin Guide & ช่อง YouTube DAY STUDIO
# ==============================================================================
elif current_page == "michelin_studio":
    render_clean_michelin_gallery(key_prefix="page5")

    st.markdown("---")
    render_html(
        """
<div class="brand-section-header">
<div>
<div class="brand-section-title">🎬 ช่อง YouTube ในเครือ DAY STUDIO</div>
<div class="brand-section-sub">ติดตามรับชมภาพยนตร์สั้นสร้างแรงบันดาลใจ สารคดีวิทยาศาสตร์อาหาร และความบันเทิงคุณภาพในเครือเดย์สตูดิโอ</div>
</div>
<div>
<span style="background:#ffffff;color:#d32f2f;padding:6px 14px;border-radius:99px;font-size:12.5px;font-weight:800;">▶️ OFFICIAL DAY STUDIO NETWORK</span>
</div>
</div>
"""
    )

    logo_b64_map = {
        "day_story": LOGO_DAY_STORY_B64,
        "day_science": LOGO_DAY_SCIENCE_B64,
        "day_home_theater": LOGO_DAY_THEATER_B64,
        "day_gold_coin": LOGO_GOLD_COIN_B64,
    }

    studio_channels = channels_cfg.get("channels", [])
    ch_cols = st.columns(3)

    for idx, ch in enumerate(studio_channels):
        col = ch_cols[idx % 3]
        ch_name = ch.get("name", "DAY STUDIO")
        ch_icon = ch.get("icon", "🎬")
        ch_sub = ch.get("subtitle", "")
        ch_desc = ch.get("description", "")
        ch_url = (ch.get("url") or "").strip()
        ch_btn_text = ch.get("button_text") or f"▶️ เข้าชมและกดติดตามช่อง {ch_name}"
        ch_coming_soon = ch.get("badge_coming_soon") or "⏳ เร็วๆ นี้ (Coming Soon)"
        logo_b64 = logo_b64_map.get(ch.get("logo_key", ""), LOGO_GOLD_COIN_B64)

        ch_logo_html = (
            f'<img src="data:image/png;base64,{logo_b64}" style="width:74px;height:74px;border-radius:16px;object-fit:cover;border:2px solid #fca5a5;box-shadow:0 6px 14px rgba(211,47,47,0.18);flex-shrink:0;" />'
            if logo_b64
            else f'<div style="font-size:46px;">{ch_icon}</div>'
        )

        if ch_url:
            action_html = (
                f'<a class="yt-red-btn" href="{ch_url}" target="_blank" rel="noopener noreferrer">{ch_btn_text}</a>'
                f'<div style="text-align:center;color:#5C4033;font-size:12px;margin-top:6px;">🔗 <a href="{ch_url}" target="_blank" style="color:#d32f2f;font-weight:700;">{ch_url}</a></div>'
            )
            status_pill = '<span style="background:#d32f2f;color:#fff;font-size:11px;font-weight:800;padding:3px 10px;border-radius:99px;">🔴 LIVE ON YOUTUBE</span>'
        else:
            action_html = f'<div class="coming-soon-badge">{ch_coming_soon}</div>'
            status_pill = '<span style="background:#fef3c7;color:#b45309;font-size:11px;font-weight:800;padding:3px 10px;border-radius:99px;border:1px solid #f59e0b;">⏳ COMING SOON</span>'

        with col:
            render_html(
                f'<div class="studio-card" style="margin-bottom:16px;"><div><div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:12px;"><span style="color:#d32f2f;font-weight:800;font-size:12.5px;">{ch_icon} DAY STUDIO OFFICIAL</span>{status_pill}</div><div style="display:flex;align-items:center;gap:14px;margin-bottom:12px;">{ch_logo_html}<div><div style="color:#b71c1c;font-size:20px;font-weight:800;line-height:1.2;">{ch_icon} {ch_name}</div><div style="color:#d32f2f;font-size:13.5px;font-weight:700;margin-top:4px;">{ch_sub}</div></div></div><div style="color:#5C4033;font-size:13.5px;line-height:1.55;margin-bottom:18px;">{ch_desc}</div></div><div>{action_html}</div></div>'
            )


# ==============================================================================
# CLEAN BRAND FOOTER
# ==============================================================================
st.markdown("<div style='height:12px;'></div>", unsafe_allow_html=True)

render_html(
    """
<div style="text-align:center;color:#5C4033;font-size:13.5px;margin-top:12px;padding:18px;border-top:2px solid #f3dfd3;background:#FFFFFF;border-radius:18px;box-shadow:0 4px 14px rgba(211,47,47,0.06);">
🍦 <b>บริษัท เดย์อินเตอร์ฟู๊ดส์ จำกัด (สำนักงานใหญ่ เดย์ ไอศกรีม)</b> • 188/10 ถ.รถไฟตะวันตก ต.พระปฐมเจดีย์ อ.เมือง จ.นครปฐม 73000<br>
📞 โทรสั่งไอศกรีม / สมัครแฟรนไชส์: <b style="color:#d32f2f;">086-3328091</b>, 063-2081237, 034-255958 • 💬 LINE Official: <b style="color:#059669;">Dayinterfood</b> • 📲 แอปสั่งซื้อ: <a href="https://app.dayicecream.com" target="_blank" style="color:#d32f2f;font-weight:800;">app.dayicecream.com</a> • 🌐 เว็บไซต์หลัก: <a href="https://www.dayicecream.com" target="_blank" style="color:#d32f2f;font-weight:700;">www.dayicecream.com</a>
</div>
"""
)
