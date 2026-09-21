import CategoricalInterventionsProofs.SAPass.Check
import CategoricalInterventionsProofs.SAPass.Common
import CategoricalInterventionsProofs.SAPass.C01_Compose
import CategoricalInterventionsProofs.SAPass.C02_Order
import CategoricalInterventionsProofs.SAPass.C03_Conflicts
import CategoricalInterventionsProofs.SAPass.C04_Pairs
import CategoricalInterventionsProofs.SAPass.C05_Factors
import CategoricalInterventionsProofs.SAPass.C06_AffinePCM
import CategoricalInterventionsProofs.SAPass.C07_AffineAction
import CategoricalInterventionsProofs.SAPass.C08_Epochs
import CategoricalInterventionsProofs.SAPass.C09_Refine
import CategoricalInterventionsProofs.SAPass.C10_Persistent
import CategoricalInterventionsProofs.SAPass.C11_Cumulative
import CategoricalInterventionsProofs.SAPass.C12_Support
import CategoricalInterventionsProofs.SAPass.C13_Identity
import CategoricalInterventionsProofs.SAPass.C14_Append
import CategoricalInterventionsProofs.SAPass.C15_Pullback
import CategoricalInterventionsProofs.SAPass.C16_Piecewise
import CategoricalInterventionsProofs.SAPass.C17_Lowering
import CategoricalInterventionsProofs.SAPass.C18_Transfer
import CategoricalInterventionsProofs.SAPass.C19_Pulses
import CategoricalInterventionsProofs.SAPass.C20_Pushforward
import CategoricalInterventionsProofs.SAPass.C21_Lift
import CategoricalInterventionsProofs.SAPass.C22_Augment
import CategoricalInterventionsProofs.SAPass.C23_Infer
import CategoricalInterventionsProofs.SAPass.C24_Strengthened
import CategoricalInterventionsProofs.SAPass.C25_Shift

/-!
# SA-Pass semantic-alignment audit

Shadow sets, forward/backward checkers and the `sa_check_*` meta-commands for
the SA-Pass procedure (Han et al., *ShadowBench*, arXiv:2608.29270) applied to
the 23 natural-language claims of `docs/ledger.jl`.  See `design/SA-PASS.md`
for the method, the per-theorem scores and the alignment gaps.

Every `sa_check_*` command below fails the build if a checker uses a forbidden
constant or does not state exactly the target/shadow it claims to.
-/
