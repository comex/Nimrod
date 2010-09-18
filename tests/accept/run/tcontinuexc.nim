type
  ESomething = object of E_Base
  ESomeOtherErr = object of E_Base

proc genErrors(s: string) =
  if s == "error!":
    raise newException(ESomething, "Test")
  else:
    raise newException(EsomeotherErr, "bla")

try:
  for i in 0..3:
    try:
      genErrors("error!")
    except ESomething:
      echo("Error happened")
    echo "came here"
    raise newException(EsomeotherErr, "bla")
finally:  
  echo "caught"

