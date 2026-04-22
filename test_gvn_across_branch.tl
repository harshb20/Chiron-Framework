:x = 1
:y = 2
if (:x > 0) [
    :a = :x + :y
    forward :a
] else [
    :b = :x + :y
    forward :b
]
:c = :x + :y
forward :c
