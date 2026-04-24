:x = 10
:y = 5
:dead1 = :x + :y
:dist = :x + 20
:dead2 = :dead1 * 3
:angle = 90
forward :dist
:dead3 = :angle + :dead2
right :angle
:gx = :dist + 1
:gy = :angle + 2
goto (:gx, :gy)
:dead4 = :gy * 9
