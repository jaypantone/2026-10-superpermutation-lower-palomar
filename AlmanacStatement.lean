import AlmanacDefs
/-! The Almanac's statement (written by the site; the judge writes this file over any
file of the same name): Every 12-symbol superpermutation has length at least 522622380 -/
namespace Almanac
def Claim : Prop := LowerBoundAt 12 522622380
end Almanac
