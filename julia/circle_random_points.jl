using Random
using Distributions

function pick_point_on_circle()
  θ = rand(Uniform(0, 2 * pi))
  x = sin(θ)
  y = cos(θ)
  (x, y)
end

function distance(a, b)
  function pow(x)
    x * x
  end
  (x1, y1) = a
  (x2, y2) = b
  sqrt(pow(x2 - x1) + pow(y2 - y1))
end

# pick random two points on a circle, compute their distance, how many chance that the distance is longer than √3
# The answer should close to 1/3
C = sqrt(3)
bigger = 0
for i in range(0, 1000)
  a = pick_point_on_circle()
  b = pick_point_on_circle()
  if distance(a, b) >= C
    global bigger = bigger + 1
  end
  distribution = bigger / i
  @show distribution
end
