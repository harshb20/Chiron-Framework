:flag = 1
:dist = 30
if (:flag == 1) [
    :step = :dist + 10
    forward :step
] else [
    :step = 5
    right 180
]
:after = :step + 2
forward :after
