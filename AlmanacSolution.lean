import AlmanacStatement
import AlmanacAdapter

/-- Fixed finite alternative: select a lower bound at n = 10. -/
theorem almanac_claim : Almanac.Claim := AlmanacAdapter.lower10
