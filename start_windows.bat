@echo off
cd /d "%~dp0"
if not exist "data" mkdir data
if not exist ".env" (
    if exist ".env.example" copy /Y ".env.example" ".env" >nul
)
echo =================================================================
echo  SIG CASINO LIVE SERVER STARTING ON http://localhost:4000
echo  - Player Panel : http://localhost:4000/
echo  - Admin Panel  : http://localhost:4000/admin
echo  - Gregmorn Hook: http://localhost:4000/api/wallet/callback
echo =================================================================
python -m pip install -r requirements.txt >nul 2>&1
python gregmorn_callback_api.py
pause
