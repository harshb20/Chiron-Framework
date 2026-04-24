:x = 4
:y = 6
:a = :x + :y
:b = :y + :x
:c = :x + :y
forward :c
:x = :x + 1
:d = :x + :y
:e = :y + :x
right :e
