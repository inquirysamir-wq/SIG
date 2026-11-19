@echo off
cd /d "%~dp0"
echo =================================================================
echo  SIG CASINO - ONE-CLICK GITHUB PUSH (WINDOWS)
echo =================================================================
set /p REPO_URL="Paste your GitHub Repository URL (e.g. https://github.com/user/repo.git): "
git init
git add -A
git commit -m "SIG Casino v110: Atomic SQLite Wallet, Instant Deposit Sync & Clean Profile Icons"
git branch -M main
git remote remove origin >nul 2>&1
git remote add origin %REPO_URL%
git push -u origin main --force
echo =================================================================
echo  SUCCESS! Pushed latest files to GitHub main branch.
echo =================================================================
pause
