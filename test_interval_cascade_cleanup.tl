:x = 10
if (:x < 20) [
    :y = 15
] else [
    :y = 100
]
if (:y < 50) [
    forward :y
] else [
    right :y
]
