if (:input > 0) [
    :speed = 4
] else [
    :speed = 8
]
if (:speed < 10) [
    :dist = :speed + 2
] else [
    :dist = 100
]
if (:dist < 20) [
    forward :dist
] else [
    right :dist
]
