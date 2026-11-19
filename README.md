# SIG Casino — Live Production Repository (Player Panel + Admin Panel + Gregmorn Hub Seamless Wallet)

Production-ready casino platform featuring a standalone **Player Panel** (`index.html` / `player_panel.html`), standalone **Admin Control Panel** (`admin.html` / `admin_panel.html`), and a **Python Flask + SQLite WAL Seamless Wallet Backend** (`gregmorn_callback_api.py`) integrated with the **Gregmorn Hub API**.

## 1. Repository Structure

| File / Folder | Purpose | 
| ----- | ----- | 
| `index.html` / `player_panel.html` | Standalone Player Casino Frontend (Lobby, Live Casino, Slots, Sports, Wallet, 1x Wager Bar, Losing Commission) | 
| `admin.html` / `admin_panel.html` | Standalone Admin Control Panel (Overview, Cashier Orders, KYC Review, Players, QR Manager, Game API, Accounting P&L) | 
| `gregmorn_callback_api.py` | Python Flask + SQLite WAL Seamless Wallet Server (`GregmornClient` + `POST /api/wallet/callback` + `/api/v1/state/sync`) | 
| `static/` | Frontend scripts (`sig_app.js`, `sig_admin.js`) and visual assets | 
| `requirements.txt` | Python production dependencies (`Flask`, `gunicorn`, `requests`) | 
| `.env.example` | Environment variable template for your Gregmorn Hub credentials | 
| `start.sh` | One-command startup script for Linux / macOS VPS | 
| `Dockerfile` & `docker-compose.yml` | One-command Docker production setup with persistent SQLite volume | 

## 2. Push to GitHub in 60 Seconds

Unzip `sig-casino-github-ready.zip` into a folder on your computer, open your terminal inside that folder, and run:

```
git init
git add .
git commit -m "Initial live launch of SIG Casino & Gregmorn Seamless Wallet"
git branch -M main
git remote add origin https://github.com/YOUR_GITHUB_USERNAME/YOUR_REPO_NAME.git
git push -u origin main

```

*(Note: `.gitignore` automatically protects your `.env` secrets and live `data/*.db` SQLite database from being pushed to GitHub.)*

## 3. Run Locally or on Your VPS (Ubuntu / Debian)

### Option A: One-Command Launch (`start.sh`)

```
git clone https://github.com/YOUR_GITHUB_USERNAME/YOUR_REPO_NAME.git
cd YOUR_REPO_NAME
cp .env.example .env
nano .env   # Paste your GREGMORN_USER_SECRET, GREGMORN_LOGIN, GREGMORN_PASSWORD
chmod +x start.sh
./start.sh

```

### Option B: Direct Python / Gunicorn Launch

```
pip install -r requirements.txt
export GREGMORN_USER_SECRET="your_gregmorn_secret"
export PORT=4000
gunicorn -w 1 --threads 8 --timeout 60 -b 0.0.0.0:4000 gregmorn_callback_api:app

```

*(Or run `python3 gregmorn_callback_api.py` — it includes a built-in zero-dependency HTTP server fallback if Flask/Gunicorn are not installed.)*

### Option C: One-Command Docker Launch

```
cp .env.example .env
docker compose up -d --build

```

## 4. Key URLs Once Running

| Route | Description | 
| ----- | ----- | 
| `https://yourdomain.com/` | **Player Panel** (Lobby, Games, Deposit, Withdraw with 1x Wager Progress Bar, Losing Commission) | 
| `https://yourdomain.com/admin` | **Admin Control Panel** (Cashier Approvals, KYC Queue, QR Manager, Game API, Table P&L) | 
| `https://yourdomain.com/api/wallet/callback` | **Gregmorn Hub Seamless Wallet Webhook** (`getBalance`, `writeBet`, `rollback` with `X-Signature` HMAC-SHA256) | 
| `https://yourdomain.com/api/v1/health` | Health check endpoint (`{"ok": true, "status": "HEALTHY"}`) | 

## 5. Details to Send Your Game Provider (Gregmorn Hub)

1. **Site Link**: `https://yourdomain.com`

2. **Server IP**: Your VPS public IPv4 address (run `curl -4 ifconfig.me` on your VPS to see it)

3. **Callback URL**: `https://yourdomain.com/api/wallet/callback`

4. **Admin Panel Username**: `sig_admin`

5. **Currency**: `USD` (or `NPR`)

## 6. Institutional Admin Role Passwords (`/admin`)

| Department / Role | Password | Permitted Modules |
| ----- | ----- | ----- |
| **Full Control (Super Admin)** | `sameer@1231` | All modules (`Overview`, `Cashier`, `Casino & Finance / P&L / Game Gateway`, `Payment Details & QR`, `Bonus & Promo`, `Players & KYC`, `Support`, `Settings`) |
| **Cashier & Finance Cage** | `cashier@1231` | `Overview`, `Cashier` (Deposits, Withdrawals, Date-Wise Transactions), `Payment Details & QR Manager` |
| **KYC & Compliance Desk** | `kyc@1231` | `Overview`, `Players Directory` & `KYC Verification Requests` |
| **Casino & Game Operations** | `manager@1231` | `Overview`, `Table P&L`, `Game Control & Provider Gateway`, `Bonus & Promo` |
| **Player Support Desk** | `support@1231` | `Overview`, `Support Chats`, `Players Directory` |
