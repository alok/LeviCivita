import LeviCivita.Analysis
open LeviCivita.Fast.FastLC

-- gradient of a 4D hypersphere SDF |x| - 1 at (3,4,0,0)/... = unit radial vector
#eval grad (n := 4) (fun v => norm v - 1) (fun i => #[0.6, 0.8, 0.0, 0.0][i.val]!)
#eval grad (n := 2) (fun v => max (v 0) (v 1)) (fun _ => 1.0)  -- tie: picks larger derivative branch
#eval sqrt (ofFloat 4 + epsilon)
#eval sqrt epsilon
#eval (abs (ofFloat 0 - epsilon) : LC)
#eval decide ((1 : LC) < 1 + epsilon)
