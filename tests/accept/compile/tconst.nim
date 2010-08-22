type TFoo = object
    foo: int

var a : const ref TFoo
var b : const ref ref TFoo

(b^).foo = 7

if a.foo == (b^).foo:
    echo("==")
else:
    echo("!=")
