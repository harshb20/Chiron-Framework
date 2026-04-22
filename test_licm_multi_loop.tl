:a = 20
:b = 5
:i = 0
repeat 3 [
    :h1 = :a + :b
    forward :h1
    right 90
]
repeat 4 [
    :variant = :i + :b
    forward :variant
    :i = :i + 1
    left 45
]
repeat 2 [
    :blocked = :a / :b
    forward :blocked
    right 180
]
