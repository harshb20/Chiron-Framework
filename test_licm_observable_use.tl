:x = 25
:y = 40
repeat 3 [
    :gx = :x + 10
    :gy = :y + 5
    penup
    goto (:gx, :gy)
    pendown
    forward :gx
    right :gy
]
