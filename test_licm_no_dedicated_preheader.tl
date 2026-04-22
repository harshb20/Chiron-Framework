:flag = 1
:base = 10
if (:flag > 0) [
    forward 1
] else [
    right 1
]
repeat 3 [
    :candidate = :base + 5
    forward :candidate
    right 90
]
