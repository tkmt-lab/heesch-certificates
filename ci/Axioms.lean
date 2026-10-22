import Heesch.Solution
import Heesch.SquareEq

/-! Prints the axioms of the main declarations of this release.
CI fails unless every line lists only `propext`, `Classical.choice`, `Quot.sound`. -/

#print axioms Heesch.hh_sound_square
#print axioms Heesch.hc_sound_square
#print axioms Heesch.hh_sound_hex
#print axioms Heesch.hc_sound_hex
#print axioms Heesch.hh_sound_tri
#print axioms Heesch.hc_sound_tri
#print axioms HeeschProof.cnfOrd_square
