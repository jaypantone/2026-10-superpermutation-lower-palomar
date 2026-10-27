import AlmanacDefs
/-! The Almanac's statement (written by the site; the judge writes this file over any
file of the same name): Every 14-symbol superpermutation has length at least 93891141150 -/
namespace Almanac
def Claim : Prop := LowerBoundAt 14 93891141150
end Almanac
