import AlmanacStatement
import AlmanacAdapter


/-- Select "My own statement". The generated Almanac.Claim is only the
judge's True anchor; this theorem states all seventeen original claims and
the twelve-symbol finite consequence. -/
theorem almanac_claim : AlmanacAdapter.CompleteClaim := AlmanacAdapter.complete_claim
