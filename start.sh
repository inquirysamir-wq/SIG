#!/usr/bin/env bash
set -e

cd "$(dirname "$0")"

mkdir -p data

if [ ! -f ".env" ] && [ -f ".env.example" ]; then
  cp .env.example .env
  echo "[SIG Casino] Created .env from .env.example (remember to set GREGMORN_USER_SECRET)."
fi

if [ -f ".env" ]; then
  set -a
  source .env
  set +a
fi

if command -v python3 >/dev/null 2>&1; then
  if [ ! -d ".venv" ]; then
    python3 -m venv .venv || true
  fi
  if [ -f ".venv/bin/activate" ]; then
    source .venv/bin/activate
    pip install --upgrade pip >/dev/null 2>&1 || true
    pip install -r requirements.txt >/dev/null 2>&1 || true
  fi
fi

PORT="${PORT:-4000}"
echo "================================================================="
echo " SIG CASINO LIVE SERVER STARTING ON PORT ${PORT}"
echo " - Player Panel : http://localhost:${PORT}/"
echo " - Admin Panel  : http://localhost:${PORT}/admin"
echo " - Gregmorn Hook: http://localhost:${PORT}/api/wallet/callback"
echo "================================================================="

if command -v gunicorn >/dev/null 2>&1; then
  exec gunicorn -w 1 --threads 8 --timeout 60 -b "0.0.0.0:${PORT}" gregmorn_callback_api:app
else
  exec python3 gregmorn_callback_api.py
fi
