import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Algebra.Equiv.TransferInstance

open scoped ComplexOrder
open ContinuousLinearMap




noncomputable section

section


variable {X : Type*}
variable {𝕜 : Type*}[RCLike 𝕜] --ℝ or ℂ

local notation :90 "†" => starRingEnd 𝕜



def isinfPosDef (K : X → X → 𝕜) : Prop :=
  ∀ (s : Finset X), Matrix.PosDef (fun (x:s) (y:s) ↦ K x y)

def isinfPosSemidef (K : X → X → 𝕜) : Prop :=
  ∀ (s : Finset X), Matrix.PosSemidef (fun (x:s) (y:s) ↦ K x y)



class infPosSemidef (K : X → X → 𝕜) where
  pos : isinfPosSemidef K

lemma PosSemiDef_of_Posdef (K : X → X → 𝕜) (h: isinfPosDef K) : isinfPosSemidef K := by
  simp[isinfPosDef,isinfPosSemidef] at *
  intro s
  exact Matrix.PosDef.posSemidef (h s)




lemma isinfPosSemidef_conj_symm (K : X → X → 𝕜) [h : infPosSemidef K] (x y : X): (†) (K y x) = K x y := by
  let s' : Set X := {x,y}
  let s : Finset X := Set.Finite.toFinset (Set.toFinite s')
  have xins : x ∈ s := by
    apply (Set.Finite.mem_toFinset (Set.toFinite s')).mpr
    exact Set.mem_insert x {y}
  have yins : y ∈ s := by
    apply (Set.Finite.mem_toFinset (Set.toFinite s')).mpr
    exact Set.mem_insert_of_mem x rfl
  exact Matrix.IsHermitian.apply (h.1 s).1 ⟨x,xins⟩ ⟨y,yins⟩

def Equiv_of_ContinuousLinear_of_self : (𝕜 →L[𝕜] 𝕜) ≃ₗᵢ[𝕜] 𝕜 where
  toFun := fun f ↦ f 1
  map_add' := by simp
  map_smul':= by simp
  invFun := fun x ↦ x•(id 𝕜 𝕜)
  left_inv := by intro f; ext; simp
  right_inv := by intro x; simp
  norm_map' := by
    intro h
    refine Eq.symm (homothety_norm h ?_)
    intro x
    nth_rw 1 [←mul_one x, ←smul_eq_mul]
    rw[(map_smul_of_tower h x 1)]
    simp[mul_comm]
end

section




variable (𝕜 : Type*)[RCLike 𝕜] --ℝ or ℂ
variable (X : outParam Type*) --Domain
variable (V : outParam Type*)[NormedAddCommGroup V][InnerProductSpace 𝕜 V]--Co-domain
variable (H : Type*)[NormedAddCommGroup H][InnerProductSpace 𝕜 H] --Our space of functions


/-
Class of vector valued Reproducing Kernel Hilbert Spaces.
-/
class vvRKHS where
  toFuns : H →ₗ[𝕜] (X → V)
  toFuns_injective : Function.Injective (toFuns : H → X → V)
  continuous_eval' : ∀ (x : X), Continuous (fun (f : H) ↦ toFuns f x)

abbrev RKHS := vvRKHS 𝕜 X 𝕜 H

end
namespace vvRKHS

open InnerProductSpace


variable {𝕜 : Type*}[RCLike 𝕜] --ℝ or ℂ
variable {X : outParam Type*} --Domain
variable {V : outParam Type*}[NormedAddCommGroup V][InnerProductSpace 𝕜 V] --Co-domain
variable {H : Type*}[NormedAddCommGroup H][InnerProductSpace 𝕜 H] --Our space of functions
local notation :90 "†" => starRingEnd 𝕜


instance toFun [inst: vvRKHS 𝕜 X V H]: FunLike H X V where
  coe := fun f ↦ toFuns f
  coe_injective' := inst.toFuns_injective



@[simp]
lemma add_apply [inst : vvRKHS 𝕜 X V H] (f g : H) (x : X) : (f + g) x = f x + g x := by
  have toFunsdef (h : H): h x = inst.toFuns h x := by rfl
  simp[toFunsdef]

@[simp]
lemma smul_apply [inst : vvRKHS 𝕜 X V H] (f : H) (x : X) (c : 𝕜): (c • f) x = c  • (f x) := by
  have toFunsdef (h : H): h x = inst.toFuns h x := by rfl
  simp[toFunsdef]

@[simp]
lemma sub_apply [inst : vvRKHS 𝕜 X V H] (f g : H) (x : X) : (f - g) x = f x - g x := by
  have toFunsdef (h : H): h x = inst.toFuns h x := by rfl
  simp[toFunsdef]


@[simp]
lemma zerofun_apply [inst : vvRKHS 𝕜 X V H] (x : X) : (0 : H) x = 0 := by
  have toFunsdef (h : H): h x = inst.toFuns h x := by rfl
  simp[toFunsdef]


@[simp]
lemma continuous_eval [inst : vvRKHS 𝕜 X V H] : ∀ (x : X), Continuous (fun (f : H) ↦ f x) := inst.continuous_eval'


lemma bounded_eval [inst : vvRKHS 𝕜 X V H] : ∀ (x : X), IsBoundedLinearMap 𝕜 (fun (f : H) ↦ f x) := by
  intro x
  apply (IsBoundedLinearMap.isLinearMap_and_continuous_iff_isBoundedLinearMap (fun (f:H) ↦ f x)).mp
  constructor
  · constructor
    <;> simp
  · exact continuous_eval x

def eval [inst : vvRKHS 𝕜 X V H] (x : X) : H →L[𝕜] V := IsBoundedLinearMap.toContinuousLinearMap (bounded_eval x)

lemma eval_apply [inst : vvRKHS 𝕜 X V H] (f : H)(x : X): inst.eval x f = f x := by rfl


variable [CompleteSpace H][CompleteSpace V]

def vvKernel [inst : vvRKHS 𝕜 X V H] (x : X) (y : X) : V →L[𝕜] V :=  (inst.eval x) ∘L (adjoint (inst.eval y))


def Kernel [inst : RKHS 𝕜 X H] (x : X)(y : X) : 𝕜 := Equiv_of_ContinuousLinear_of_self (inst.vvKernel x y)


def Kerfun [inst : RKHS 𝕜 X H] (x : X) : H := (toDual 𝕜 H).symm (eval x)


lemma Kerfun_apply' [inst : RKHS 𝕜 X H] (x : X) (f : H) :  ⟪inst.Kerfun x, f⟫_𝕜 = (inst.eval x) f := by
  simp[Kerfun]

@[simp]
lemma Kerfun_apply [inst : RKHS 𝕜 X H] (x : X) (f : H) :  ⟪inst.Kerfun x, f⟫_𝕜 = f x := by
  simp[Kerfun]
  rfl

lemma Kernel_inner [inst : RKHS 𝕜 X H] (x y : X) : inst.Kernel x y = ⟪inst.Kerfun x, inst.Kerfun y⟫_𝕜 := by
  simp[Kernel,Kerfun,Equiv_of_ContinuousLinear_of_self,vvKernel]
  apply congrArg
  apply ext_inner_right 𝕜
  intro f
  rw[adjoint_inner_left]
  simp


lemma Kerfun_to_Kernelspec [inst : RKHS 𝕜 X H] (y : X) : inst.Kerfun y = fun x ↦ inst.Kernel x y := by
  ext x
  rw[←Kerfun_apply x (Kerfun y),Kernel_inner]



open Submodule





theorem Kerfun_dense [inst : RKHS 𝕜 X H]: topologicalClosure (Submodule.span 𝕜 {inst.Kerfun x | x}) = ⊤ := by
  set S := {inst.Kerfun x | x}
  set V := Submodule.span 𝕜 S
  set Vc := topologicalClosure V
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply (Submodule.eq_bot_iff Vcᗮ).mpr
  intro f fin
  apply DFunLike.ext f
  simp
  intro y
  have : inst.Kerfun y ∈ S := by simp[S]
  have : inst.Kerfun y ∈ V := mem_span.mpr fun _ a ↦ a this
  have : inst.Kerfun y ∈ Vc := subset_closure this
  have := Submodule.inner_right_of_mem_orthogonal this fin
  simp at this
  exact this



instance KernelPosSemidef [inst : RKHS 𝕜 X H]: infPosSemidef (inst.Kernel) where
  pos := by
    intro s
    constructor
    · apply Matrix.IsHermitian.ext_iff.mpr
      simp [Kernel_inner, -Kerfun_apply]
    · intro x
      simp only [Matrix.mulVec, dotProduct, Kernel_inner,Pi.star_apply, RCLike.star_def]
      conv =>
        arg 2; arg 2
        intro j
        rw[Finset.mul_sum]
        conv =>
          arg 2
          intro i
          rw[←mul_assoc,← smul_left, mul_comm,←inner_smul_right]
        rw[← inner_sum]
      rw[← sum_inner]
      apply RCLike.le_iff_re_im.mpr
      rw[← norm_sq_eq_re_inner]
      simp

lemma conj_symm [inst : RKHS 𝕜 X H] (x y : X): (†) (inst.Kernel y x) = inst.Kernel x y :=
  isinfPosSemidef_conj_symm Kernel x y


end vvRKHS

section


variable {X : Type*}
variable {𝕜 : Type*}[RCLike 𝕜] --ℝ or ℂ
local notation :90 "†" => starRingEnd 𝕜


open Classical
open InnerProductSpace
open scoped TensorProduct
open Function Set
open Submodule




variable (K : X → X → 𝕜)


def s : Set (X → 𝕜) := {(fun x ↦ K x y) | y}

def 𝓛 := span 𝕜 (s K)


lemma spanspan : ⊤ ≤ span 𝕜 ((Subtype.val ⁻¹' (s K)): Set ↥(span 𝕜 (s K))) := by
  have: span 𝕜 (Subtype.val ⁻¹' (s K)) = ⊤ := @span_span_coe_preimage 𝕜 (X → 𝕜) _ _ _ (s K)
  rw[←this]


private def B' := @Basis.ofSpan 𝕜 (𝓛 K) _ _ _ (Subtype.val ⁻¹' s K) (spanspan K)
private def bel: (∅: Set ↥(𝓛 K)) ⊆ Subtype.val ⁻¹' s K → Set ↥(𝓛 K) := (linearIndepOn_empty 𝕜 (_root_.id : ↥(𝓛 K) → ↥(𝓛 K))).extend
private def Bel: Set ↥(𝓛 K) := (bel K) (empty_subset (Subtype.val ⁻¹' s K)) --Basis elements
private def B: Basis (Bel K) 𝕜 (𝓛 K) := B' K


lemma inBel (i: (Bel K)): (B K) i ∈ (Bel K) := by
  have: Set.range (B K) = Bel K :=
    Basis.range_ofSpan (spanspan K)
  have (i: (Bel K)): (B K) i ∈ Set.range (B K) :=
    mem_range_self i
  simp_all only [Subtype.forall]


lemma subst: Bel K ⊆ Subtype.val ⁻¹' s K := by
  have rangeeq : Set.range ⇑(Basis.ofSpan (spanspan K)) = (Bel K) :=
    Basis.range_ofSpan (spanspan K)
  have := Basis.ofSpan_subset (spanspan K)
  rw[rangeeq] at this
  exact this






def s_to_X : s K → X := fun k ↦ choose k.2
def Bel_to_s : Bel K → s K := fun f ↦ ⟨f.1,(subst K) f.2⟩
def Bel_to_Bel : Bel K → Bel K :=fun i ↦ ⟨B K i,inBel K i⟩


def Bel_to_X : Bel K → X := (s_to_X K) ∘ (Bel_to_s K) ∘ (Bel_to_Bel K)

lemma injBel_to_X : Injective (Bel_to_X K):= by
  have injX : Injective (s_to_X K) := by
    intro k1 k2 keq
    simp [s_to_X] at keq
    have h1 := choose_spec k1.2
    have h2 := choose_spec k2.2
    have : (k1 : X → 𝕜) = k2 := by
      rw[←h1,←h2,keq]
    exact SetCoe.ext this
  have injs : Injective (Bel_to_s K):= by
    intro f1 f2 feq
    simp [Bel_to_s] at feq
    exact SetCoe.ext feq
  have injBel : Injective (Bel_to_Bel K) := by
    intro i1 i2 ieq
    simp[Bel_to_Bel] at ieq
    exact ((B K).injective) ieq
  exact injX.comp (injs.comp injBel)



instance KerneltoPreInnerCore [pos : infPosSemidef K]: PreInnerProductSpace.Core 𝕜 (𝓛 K) where
  inner := fun f ↦ fun g ↦
    ∑ i ∈ ((B K).repr f).support, ∑ j ∈ ((B K).repr g).support,
    (†) ((B K).repr f i) • (B K).repr g j • K (Bel_to_X K i) (Bel_to_X K j)
  conj_inner_symm := by
    intro f g
    simp
    set Cf := (B K).repr f
    set Cg := (B K).repr g
    rw[Finset.sum_comm]
    conv =>
      left; right
      intro i
      right
      intro j
      rw[isinfPosSemidef_conj_symm K,←mul_assoc,mul_comm (Cg j),mul_assoc]
  add_left := by
    intro f g h
    set cf := (B K).repr f
    set cfg:= (B K).repr (f +g)
    set cg := (B K).repr g
    have cfgrw: cfg = cf + cg := by simp[cf,cfg,cg]
    let U := cf.support ∪ cfg.support ∪ cg.support
    have fsub: cf.support ⊆ U := by simp[U]
    have fgsub: cg.support ⊆ U := by unfold U; exact Finset.subset_union_right
    have gsub: cfg.support ⊆ U := by simp[U]; rw[Finset.union_comm]; simp
    rw[Finset.sum_subset fsub _,Finset.sum_subset fgsub _,Finset.sum_subset gsub _,cfgrw]
    conv =>
      right
      rw[←Finset.sum_add_distrib]
      right
      intro i
      rw[←Finset.sum_add_distrib]
      right
      intro j
      rw[←add_smul]
    simp
    · intro i _ inotin
      rw[Finsupp.notMem_support_iff.mp inotin]
      simp
    · intro i _ inotin
      rw[Finsupp.notMem_support_iff.mp inotin]
      simp
    · intro i _ inotin
      rw[Finsupp.notMem_support_iff.mp inotin]
      simp
  smul_left := by
    intro f g r
    by_cases h : r = 0
    · simp[h]
    have : ((B K).repr (r • f)).support = ((B K).repr (f)).support := by
      ext x
      simp[Finsupp.mem_support_iff]
      intro temp
      exact h
    rw[this]
    simp[Finset.mul_sum,mul_assoc]
  re_inner_nonneg := by
    intro f
    set T1 := Bel_to_X K --Injection from Bel to X
    set cf: (Bel K) →₀ 𝕜   := (B K).repr f --Coefficients of f
    set S: Finset ↑(Bel K) := cf.support --Support of cf
    let c: S → 𝕜  := Finset.restrict S cf --Coefficients as function from S
    set S': Finset X := Finset.image T1 S --Image T(S)
    let T2: S → X := Finset.restrict S T1
    have Teq (x : S): T1 x = T2 x := rfl
    have Tim (i : S): T2 i ∈ Finset.image T1 S := by
      rw[←Teq]
      apply Finset.mem_image.mpr
      use i
      simp
    set T : S → S' := fun i ↦ ⟨T2 i, Tim i⟩
    have Teq'(i : S): T i = T2 i := rfl
    have Tbij : Bijective T := by
      constructor
      · intro i1 i2 ieq
        replace ieq : (T i1).1 = (T i2).1 := congrArg Subtype.val ieq
        rw[Teq' i1,Teq' i2] at ieq
        exact Subtype.eq ((injBel_to_X K) ieq)
      · intro x
        obtain ⟨i,iin,ieq⟩ := Finset.mem_image.mp x.2
        use ⟨i,iin⟩
        exact Subtype.eq ieq
    obtain ⟨Tinv, linv, rinv⟩ := Function.bijective_iff_has_inverse.mp Tbij
    let c' := c ∘ Tinv
    have := (pos.1 S').2 c'
    simp[dotProduct,Matrix.mulVec] at this

    have sumeq: ∑ x ∈ S'.attach, (†) (c' x) * ∑ x_1 ∈ S'.attach, K ↑x ↑x_1 * c' x_1 =
      ∑ i ∈ S, ∑ j ∈ S, (†) (cf i) • cf j • K (T1 i) (T1 j) := by
      conv =>
        left; right
        intro x
        rw[Finset.mul_sum]
        right
        intro x_1
        rw[←mul_assoc, mul_comm,←mul_assoc,←@Algebra.id.smul_eq_mul,←@Algebra.id.smul_eq_mul]
      refine Finset.sum_of_injOn (fun i ↦ Tinv i) (fun ⦃x₁⦄ ↦ ?_) ?_ ?_ ?_
      · intro x1in x₂ x2in Tinveq
        simp at Tinveq
        have : Tinv x₁ = Tinv x₂ := by exact Subtype.eq Tinveq
        have : T (Tinv x₁) = T (Tinv x₂) := by exact congrArg T this
        rw[rinv x₁,rinv x₂] at this
        exact this
      · simp
      · intro i iin inotin
        have : i ∈ (fun i ↦ ↑(Tinv i)) '' ↑S'.attach := by
          use (T ⟨i,iin⟩)
          simp
          rw[linv ⟨i,iin⟩]
        trivial
      · intro i iin
        refine Finset.sum_of_injOn (fun i ↦ Tinv i) (fun ⦃x₁⦄ ↦ ?_) ?_ ?_ ?_
        · intro x1in x₂ x2in Tinveq
          simp at Tinveq
          have : Tinv x₁ = Tinv x₂ := by exact Subtype.eq Tinveq
          have : T (Tinv x₁) = T (Tinv x₂) := by exact congrArg T this
          rw[rinv x₁,rinv x₂] at this
          exact this
        · simp
        · intro i iin inotin
          have : i ∈ (fun i ↦ ↑(Tinv i)) '' ↑S'.attach := by
            use (T ⟨i,iin⟩)
            simp
            rw[linv ⟨i,iin⟩]
          trivial
        · intro j jin
          simp[c',c]
          have (x : { x // x ∈ S' }): ↑x = T1 ↑(Tinv x) := by
            rw[Teq,←Teq', rinv]
          simp[this]
          ring
    rw[sumeq] at this
    exact (RCLike.nonneg_iff.mp this).1



instance innlinear (f: 𝓛 K)[infPosSemidef K] : 𝓛 K →ₗ[𝕜] 𝕜 where
  toFun := fun g ↦ (KerneltoPreInnerCore K).inner f g
  map_add' := by
    have := (KerneltoPreInnerCore K).add_left
    intro g1 g2
    rw[←(KerneltoPreInnerCore K).conj_inner_symm]
    rw[this,map_add]
    rw[(KerneltoPreInnerCore K).conj_inner_symm,(KerneltoPreInnerCore K).conj_inner_symm]
  map_smul' := by
    intro m g
    rw[←(KerneltoPreInnerCore K).conj_inner_symm,(KerneltoPreInnerCore K).smul_left]
    simp
    rw[(KerneltoPreInnerCore K).conj_inner_symm]
    left
    trivial



lemma ssubst : s K ⊆ 𝓛 K:= by
  exact span_le.mp fun ⦃x⦄ a ↦ a




lemma innsum (f : 𝓛 K) (s : Finset (Bel K)) (F : (Bel K) → (𝓛 K))[pos : infPosSemidef K]: (KerneltoPreInnerCore K).inner (∑ x∈s, F x) f = ∑ x∈s, (KerneltoPreInnerCore K).inner (F x) f := by
  rw[←(KerneltoPreInnerCore K).conj_inner_symm]
  have (g : 𝓛 K): (innlinear K f) g= ((KerneltoPreInnerCore K).inner f g) := rfl
  rw[←this,map_sum,map_sum]
  have (x : (Bel K)): (†) ((innlinear K f) (F x)) = (KerneltoPreInnerCore K).inner (F x) f := by
    rw[this,(KerneltoPreInnerCore K).conj_inner_symm]
  conv =>
    left; right
    intro x
    rw[this]

def Kfun (y : X):  s K := ⟨(fun x ↦ K x y),by simp[s]⟩

def Kel (y: X): 𝓛 K := ⟨Kfun K y,ssubst K (Kfun K y).2⟩


set_option linter.unusedSectionVars false
lemma stoKfun (k : s K): Kfun K (s_to_X K k) = k := by
  ext x
  have := choose_spec k.2
  set y':= choose k.2
  set y := s_to_X K k
  have yeq: y' = y := rfl
  rw[yeq] at this
  have := congrFun this x
  rw[←this]
  simp[Kfun]




lemma rep0 (i : Bel K)(j : Bel K): ((B K) i).1 (Bel_to_X K j) = K (Bel_to_X K j) (Bel_to_X K i) := by
  set T := Bel_to_X K
  let x := T i
  have : Kfun K x = ((B K) i).1 := by
    simp[x,T,Bel_to_X]
    rw[stoKfun]
    simp[Bel_to_s,Bel_to_Bel]
  rw[←this]
  simp[Kfun,x]


variable [infPosSemidef K]

lemma rep1 (i : Bel K)(f : 𝓛 K) : (KerneltoPreInnerCore K).inner (B K i) f = f.1 (Bel_to_X K i) := by
  simp[inner]
  rw [Finsupp.support_single_ne_zero _ _]
  simp
  swap
  exact one_ne_zero
  have frep := Basis.linearCombination_repr (B K) f
  simp[Finsupp.linearCombination,Finsupp.sum] at frep
  replace frep := congrFun (congrArg Subtype.val frep) (Bel_to_X K i)
  simp at frep
  rw[←frep]
  conv =>
    left; right
    intro x
    rw[←rep0 K x i]



lemma reproducing (y : X)(f : 𝓛 K): (KerneltoPreInnerCore K).inner (Kel K y) f = f.1 y := by
  have frep := Basis.linearCombination_repr (B K) f
  simp[Finsupp.linearCombination,Finsupp.sum] at frep
  rw[←frep,←(KerneltoPreInnerCore K).conj_inner_symm,innsum,map_sum]
  have (k : Bel K): (†) ((Kel K y).1 (Bel_to_X K k)) = ((B K) k).1 y := by
    simp[Bel_to_X,Kel]
    have : (B K) k = Bel_to_Bel K k := rfl
    rw[this]
    set k := Bel_to_Bel K k
    set k' := Bel_to_s K k
    have : (↑↑k : X → 𝕜) y = k'.1 y := by rfl
    rw[this]
    simp[Kfun,s_to_X]
    have := congrFun (choose_spec k'.2) y
    rw[←this,isinfPosSemidef_conj_symm K]
  conv =>
    left; right
    intro k
    rw[(KerneltoPreInnerCore K).smul_left]
    rw[rep1]
    simp
    rw[this]
  simp



instance KerneltoInnerCore : InnerProductSpace.Core 𝕜 (𝓛 K) :=
  {(KerneltoPreInnerCore K) with
  definite := by
    intro f inff0
    ext y
    simp
    rw[←reproducing K]
    have : ‖(KerneltoPreInnerCore K).inner (Kel K y) f‖ = 0 := by
      apply zero_eq_mul_self.mp
      nth_rw 2 [←(KerneltoPreInnerCore K).conj_inner_symm]
      rw[RCLike.norm_conj]
      have neg:= @Core.inner_mul_inner_self_le _ _ _ _ _ (KerneltoPreInnerCore K) (Kel K y) f
      rw[inff0] at neg
      simp at neg
      have pos: 0 ≤ ‖(KerneltoPreInnerCore K).inner (Kel K y) f‖ * ‖(KerneltoPreInnerCore K).inner f (Kel K y)‖ := by
        nth_rw 2 [←(KerneltoPreInnerCore K).conj_inner_symm]
        rw[RCLike.norm_conj]
        exact mul_self_nonneg (‖(KerneltoPreInnerCore K).inner (Kel K y) f‖)
      exact le_antisymm pos neg
    exact norm_eq_zero.mp this
  }

instance KerneltoNormedAddCommGroup : NormedAddCommGroup (𝓛 K) := (KerneltoInnerCore K).toNormedAddCommGroup


instance KerneltoInner : InnerProductSpace 𝕜 (𝓛 K) := InnerProductSpace.ofCore (KerneltoInnerCore K)



--def L : Set (X → 𝕜) := (𝓛 K)
structure L where
  val : X → 𝕜
  prop : val ∈ 𝓛 K

def equiv : L K ≃ 𝓛 K where
  toFun := fun f ↦ ⟨f.1, f.2⟩
  invFun := fun f ↦ ⟨f.1,f.2⟩
  left_inv := by
    intro f
    simp
  right_inv := by
    intro f
    simp


instance : AddCommGroup (L K) := (equiv K).addCommGroup
instance: Module 𝕜 (L K) := (equiv K).module 𝕜


instance : NormedAddCommGroup (L K) where
  norm := fun f ↦ norm (equiv K f)
  dist := fun f g ↦ dist (equiv K f) (equiv K g)
  dist_self := by
    simp
  dist_comm := fun f g ↦ dist_comm (equiv K f) (equiv K g)
  dist_triangle := fun f g h ↦ dist_triangle (equiv K f) (equiv K g) (equiv K h)
  eq_of_dist_eq_zero := by
    intro f g prop
    exact (equiv K).injective (eq_of_dist_eq_zero prop)



instance : InnerProductSpace 𝕜 (L K) where
  inner := fun f g ↦ inner 𝕜 (equiv K f) (equiv K g)
  norm_smul_le := fun m f ↦ norm_smul_le m (equiv K f)
  norm_sq_eq_re_inner := fun f ↦ norm_sq_eq_re_inner (equiv K f)
  conj_inner_symm := fun f g ↦ (KerneltoInner K).conj_inner_symm (equiv K f) (equiv K g)
  add_left := fun f g h ↦ (KerneltoInner K).add_left (equiv K f) (equiv K g) (equiv K h)
  smul_left := fun f g m ↦ (KerneltoInner K).smul_left (equiv K f) (equiv K g) m


def equiv' : L K ≃ₗᵢ[𝕜] 𝓛 K := {(equiv K) with
  map_add' := fun _ _ ↦ rfl
  map_smul' := fun _ _ ↦ rfl
  norm_map' := fun _ ↦ rfl
}

def H := UniformSpace.Completion (L K)

instance HCommGroup : NormedAddCommGroup (H K) := UniformSpace.Completion.instNormedAddCommGroup (L K)
instance HinnerProdu: InnerProductSpace 𝕜 (H K):= UniformSpace.Completion.innerProductSpace
instance HComp : CompleteSpace (H K) := UniformSpace.Completion.completeSpace (L K)



def Lkfun (x : X) := (equiv K).symm (Kel K x)

def LtoH : L K →ₗᵢ[𝕜] H K := @UniformSpace.Completion.toComplₗᵢ 𝕜 (L K) _ _ _ _

def Hkfun (x : X) : H K := (LtoH K) ((Lkfun K) x)

def KerneltoFun : H K → X → 𝕜 := fun f x ↦ ⟪Hkfun K x, f⟫_𝕜

def LL : Submodule 𝕜 (H K) where
  carrier := range (LtoH K)
  add_mem' := by
    intro f g ⟨f',feq⟩ ⟨g',geq⟩
    use (f' + g')
    simp[feq,geq]
  zero_mem' := by
    use 0
    simp
  smul_mem' := by
    intro m f ⟨f',feq⟩
    use (m•f')
    simp[feq]

lemma closureLLisH : topologicalClosure (LL K) = ⊤ := by
  refine dense_iff_topologicalClosure_eq_top.mp ?_
  exact UniformSpace.Completion.denseRange_coe



lemma KerneltoFunlin : IsLinearMap 𝕜 (KerneltoFun K) := by
  constructor
  · intro f g
    ext x
    exact inner_add_right (Hkfun K x) f g
  · intro m f
    ext x
    simp only [KerneltoFun, Pi.smul_apply]
    exact inner_smul_right_eq_smul (Hkfun K x) f m

def HlinKerfun := (KerneltoFunlin K).mk'



instance KerneltoRKHS : RKHS 𝕜 X (H K) where
  toFuns := HlinKerfun K
  toFuns_injective := by
    intro f g fgeq
    replace fgeq : (HlinKerfun K) (f - g) = 0 := by
      rw[map_sub,fgeq,sub_self]
    simp[HlinKerfun] at fgeq
    have : f-g = 0 := by
      set h := f-g
      by_cases nonzero : h = 0
      trivial
      have hpos := norm_pos_iff.mpr nonzero
      have h1: ∀f': L K, ⟪h, LtoH K f'⟫_𝕜 = 0 := by
        intro f'
        unfold KerneltoFun at fgeq
        replace fgeq : ∀x: X, ⟪Hkfun K x, h⟫_𝕜 =0 := fun x ↦ congrFun fgeq x
        let f := equiv K f'
        have f'eq : (equiv K).symm f = f' := rfl
        rw[←f'eq]
        have frep := Basis.linearCombination_repr (B K) f
        simp[Finsupp.linearCombination,Finsupp.sum] at frep
        have : (equiv K).symm f = (equiv' K).symm f := rfl
        rw[this,←frep,map_sum,map_sum,inner_sum]
        have (i : Bel K): ⟪h, (LtoH K) ((equiv' K).symm ((B K) i))⟫_𝕜 = 0 := by
          let x := Bel_to_X K i
          have : Hkfun K x = (LtoH K) ((equiv' K).symm ((B K) i)) := by
            simp[Hkfun,Lkfun]
            have : Kel K x = (B K) i := by
              have (f : 𝓛 K): inner 𝕜 (Kel K x) f = inner 𝕜 ((B K) i) f:= by
                rw[rep1,reproducing]
              exact ext_inner_right 𝕜 this
            rw[this]
            rfl
          rw[←this,←conj_inner_symm,fgeq]
          simp
        conv =>
          left; right
          intro i
          rw[map_smul,map_smul,inner_smul_right,this]
        simp
      have : ∀f'': H K, ⟪h, f''⟫_𝕜 = 0 := by
        have := closureLLisH K
        intro f
        have fin: f ∈ (⊤ : Submodule 𝕜 (H K)) := by trivial
        rw[←this] at fin
        apply Metric.mem_closure_iff.mp at fin
        simp at fin
        have : ∀ ε: ℝ, ε >0 → ‖⟪h, f⟫_𝕜‖ < ε := by
          intro ε epos
          obtain ⟨g,⟨g',geq⟩,gdist⟩ := fin (ε/‖h‖) (div_pos epos hpos)
          have : dist f g =  ‖f - g‖ := by exact NormedAddGroup.dist_eq f g
          rw[this] at gdist
          have : ⟪h, g⟫_𝕜 = 0 := by
            rw[←geq]
            exact h1 g'
          rw[←sub_add_cancel f g,inner_add_right,this,add_zero]
          calc
            ‖⟪h, f - g⟫_𝕜‖ ≤ ‖h‖ * ‖f-g‖ := by exact norm_inner_le_norm h (f-g)
            _ < ‖h‖ * (ε / ‖h‖) := by
              apply mul_lt_mul_of_pos_left gdist hpos
            _ = ε := by field_simp
        have : ‖⟪h, f⟫_𝕜‖ = 0 := by
          have neg: ‖⟪h, f⟫_𝕜‖ ≤ 0 := by
            contrapose this
            push_neg at *
            use ‖⟪h, f⟫_𝕜‖
          have pos: ‖⟪h, f⟫_𝕜‖ ≥ 0 := norm_nonneg ⟪h, f⟫_𝕜
          exact le_antisymm neg pos
        exact norm_eq_zero.mp this
      exact inner_self_eq_zero.mp (this h)

    rw[←add_zero g,←this]
    simp
  continuous_eval' := fun x ↦ (innerSL 𝕜 (Hkfun K x)).continuous

open vvRKHS

theorem Kernel_eq_Kernel : K = (KerneltoRKHS K).Kernel := by
  ext x y
  rw[Kernel_inner,Kerfun_apply]
  simp[toFun,toFuns,HlinKerfun,KerneltoFun]
  rw[←conj_inner_symm,Kerfun_apply]
  simp[toFun,toFuns,HlinKerfun,KerneltoFun,Hkfun,Lkfun]
  have : (equiv K).symm = (equiv' K).symm := rfl
  simp[this]
  rw[reproducing K]
  simp[Kel,Kfun]
