# Test new floating point exceptions

{.floatChecks: on.}

var x = 0.0
var y = 0.0

echo x / y #OUT Error: unhandled exception: FPU operation caused a NaN result [EFloatInvalidOp]
