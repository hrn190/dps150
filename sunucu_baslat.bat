@echo off
cd /d "%~dp0"
chcp 65001 >nul
title DPS-150 sunucusu
where python >nul 2>nul || (echo Python bulunamadi. OKU.txt dosyasindaki 1. adimi yapin. & pause & exit /b)
python -c "import serial" 2>nul || python -m pip install pyserial
python dps150_server.py %*
pause
