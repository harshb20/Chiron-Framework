:base = 30
:flag = 2
:turn = 60
repeat 4 [
    :dist = :base + 7
    if (:flag > 0) [
        forward :dist
        right :turn
    ] else [
        backward :dist
        left :turn
    ]
    :flag = :flag - 1
]
