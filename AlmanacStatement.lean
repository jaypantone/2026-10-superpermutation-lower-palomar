import AlmanacDefs
/-! The Almanac's statement (written by the site; the judge writes this file over any
file of the same name): Every 10-symbol superpermutation has length at least 4033379 -/
namespace Almanac
def Claim : Prop := LowerBoundAt 10 4033379
end Almanac
