module

public import Carleman.Transfer.Residual

/-! One orientation parameter, with the original signs and half-open cells. -/
@[expose] public section
namespace Carleman
inductive Orientation where
  | plus
  | minus
  deriving DecidableEq

namespace Orientation

def sign : Orientation → ℝ
  | plus => 1
  | minus => -1

noncomputable def extension (s : Orientation) (g : TimeGrid) {E : Type*}
    (u : g.Sequence E) : ℝ → E :=
  match s with
  | plus => g.extensionPlus u
  | minus => g.extensionMinus u

noncomputable def difference (s : Orientation) (g : TimeGrid) {E : Type*}
    [AddCommGroup E] [Module ℝ E] (u : g.Sequence E) : g.Sequence E :=
  match s with
  | plus => g.dPlus u
  | minus => g.dMinus u

theorem extension_apply (s : Orientation) (g : TimeGrid) {E F : Type*}
    (f : E → F) (u : g.Sequence E) (t : ℝ) :
    s.extension g (fun i => f (u i)) t = f (s.extension g u t) := by cases s <;> rfl

variable {H X F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  {V : Submodule ℝ H} {r : Reconstruction V X}

theorem state_solves_shifted (s : Orientation) (g : TimeGrid) (l : LoadInterface r F)
    (A : X →ₗ[ℝ] X) (μ : g.Sequence ℝ) (f : g.Sequence F) (z : g.Sequence X)
    (hz : s.difference g z + g.map A z = fun i => l.Γ (f i)) :
    s.difference g z + r.shiftedSpatial g A μ z =
      g.map r.J (l.transferLoad g μ f z) := by
  cases s
  · exact l.state_solves_shifted_dPlus g A μ f z hz
  · exact l.state_solves_shifted_dMinus g A μ f z hz

end Orientation
end Carleman
