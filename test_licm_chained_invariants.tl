:base = 12
:offset = 3
repeat 4 [
    :first = :base + :offset
    :second = :first * 2
    forward :second
    right :first
]
