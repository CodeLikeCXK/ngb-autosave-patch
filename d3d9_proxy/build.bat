@echo off
set VCVARS="C:\Program Files (x86)\Microsoft Visual Studio\2022\BuildTools\VC\Auxiliary\Build\vcvarsall.bat"
call %VCVARS% x86

cd /d "%~dp0"
echo Compiling 32-bit d3d9.dll proxy...

rem Exports are declared by #pragma comment(linker) in proxy_main.cpp (no .def)
cl /O2 /W3 /MT /EHsc /LD proxy_main.cpp /Fe:..\d3d9.dll /link user32.lib kernel32.lib

if %ERRORLEVEL% EQU 0 (
    echo [SUCCESS] d3d9.dll compiled and output to root directory!
) else (
    echo [ERROR] Compilation failed!
)
