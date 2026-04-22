:x = 10
if (:x < 20) [
    :y = :x + 5
    forward :y
] else [
    :y = 100
    forward :y
]
