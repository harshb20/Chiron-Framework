:base = 40
:offset = 6
:scale = 2
:angle = 30
:walk = 5
:i = 0
:j = 3
:flag = 4
:x = 10
:y = 20
penup
goto (:x, :y)
pendown
repeat 4 [
    :hoista = :base + :offset
    :hoistb = :hoista * :scale
    :deada = :offset + 100
    forward :hoistb
    right :angle
    :i = :i + 1
]
:gap = :base + 1
repeat 5 [
    :varianta = :i + :walk
    forward :varianta
    :i = :i + 1
    left :angle
    :safeconst = :base + :offset
    right :safeconst
]
repeat 3 [
    :diva = :base / :scale
    forward :diva
    :mixeda = :diva + :offset
    right :mixeda
    :j = :j + 1
]
repeat 4 [
    :branchdist = :base + :walk
    if (:flag > 2) [
        forward :branchdist
        :branchdead = :offset + :scale
        right :angle
    ] else [
        backward :branchdist
        :branchvariant = :flag + :walk
        left :angle
    ]
    :flag = :flag - 1
]
:x = :x + 5
:y = :y + 7
repeat 2 [
    :gx = :x + :base
    :gy = :y + :offset
    penup
    goto (:gx, :gy)
    pendown
    forward :gx
    right :gy
]
repeat 3 [
    :chainone = :base + :offset
    :chaintwo = :chainone + :walk
    :chainthree = :chaintwo * :scale
    forward :chainthree
    right :chainone
    left :chaintwo
]
repeat 3 [
    if (:j > 0) [
        :insidebranch = :base + :offset
        forward :insidebranch
    ] else [
        :insideelse = :walk + :offset
        backward :insideelse
    ]
    :j = :j - 1
    right :angle
]
repeat 4 [
    :carry = :j + :offset
    :j = :j + 2
    forward :carry
    if (:carry > :base) [
        right :angle
    ] else [
        left :angle
    ]
]
:final = :base + :offset
forward :final
right :angle
penup
goto (:x, :y)
pendown
