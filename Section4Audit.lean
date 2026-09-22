import Section4.ApiProbe
import Section4.SignChangeSpike

/-!
# Audit and regression umbrella

This module is a separate build target for the Task 1 API probes and the Task 2 feasibility spike.
It is intentionally distinct from the production umbrella `Section4`, so importing the finished
formalization does not expose provisional diagnostic declarations. The package's default build
includes both umbrellas.
-/
