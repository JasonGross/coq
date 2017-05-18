call MakeCoq_SetRootPath

call MakeCoq_MinGW.bat ^
  -arch=64 ^
  -installer=Y ^
  -coqver=local ^
  -destcyg=%ROOTPATH%\cygwin_coq64_git_inst ^
  -destcoq=%ROOTPATH%\coq64_git_inst ^
  -cygcache=%ROOTPATH%\cygwin_coq64_git_cache
