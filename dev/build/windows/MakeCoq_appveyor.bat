@ECHO ON

SET GITDIR_WFMT=%CD%
SET GITDIR_MFMT=%GITDIR_WFMT:\=/%
SET GITDIR_CFMT=%GITDIR_MFMT:C:/=/cygdrive/c/%
SET GITDIR_CFMT=%GITDIR_CFMT:D:/=/cygdrive/d/%
SET GITDIR_CFMT=%GITDIR_CFMT:E:/=/cygdrive/e/%
ECHO %GITDIR_WFMT%
ECHO %GITDIR_CFMT%

CD \

SET ROOTDIR_WFMT=%CD%
SET ROOTDIR_MFMT=%ROOTDIR_WFMT:\=/%
SET ROOTDIR_CFMT=%ROOTDIR_MFMT:C:/=/cygdrive/c/%
SET ROOTDIR_CFMT=%ROOTDIR_CFMT:D:/=/cygdrive/d/%
SET ROOTDIR_CFMT=%ROOTDIR_CFMT:E:/=/cygdrive/e/%
ECHO %ROOTDIR_WFMT%
ECHO %ROOTDIR_CFMT%

MKDIR cygwin
MKDIR result
MKDIR build

XCOPY %GITDIR_WFMT%\dev\build\windows build /S

CD build
DIR /S

SET COQREGTESTING=Y

SET H
SET U

appveyor DownloadFile http://cygwin.com/setup-x86_64.exe

MakeCoq_MinGW.bat -arch=64 -installer=Y -coqver=%GITDIR_CFMT% -destcyg="%ROOTDIR_WFMT%\cygwin" -destcoq="%ROOTDIR_WFMT%\result"

IF %ERRORLEVEL% NEQ 0 (
  ECHO MakeCoq failed with error code %ERRORLEVEL%
  EXIT /b %ERRORLEVEL%
)
