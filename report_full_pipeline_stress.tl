:flag = 1
:seed = :input + 2
:dead0 = :seed * 99
if (:flag == 1) [
    :start = :seed + 10
    forward :start
] else [
    :start = 1
    right 180
]
:dead1 = :dead0 + :start
:x = :seed + 3
:y = :input + 5
:sum1 = :x + :y
:sum2 = :y + :x
:sum3 = :x + :y
forward :sum3
:base = :seed + 20
:offset = 7
:k = 0
repeat 3 [
    :step = :base + :offset
    :turn = :k + :offset
    forward :step
    right :turn
    :k = :k + 1
]
:i = :seed
repeat 4 [
    :d = :i * 4
    forward :d
    :i = :i + 1
]
if (:choice > 0) [
    :speed = 4
] else [
    :speed = 8
]
if (:speed < 10) [
    :move = :speed + 2
] else [
    :move = 100
]
forward :move
:trash = :move * :dead1
right :offset
