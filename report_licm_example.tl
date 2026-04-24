:base = 20
:offset = 7
:i = 0
repeat 4 [
    :step = :base + :offset
    :turn = :i + :offset
    forward :step
    right :turn
    :i = :i + 1
]
