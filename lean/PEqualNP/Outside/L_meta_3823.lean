import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3823

namespace FirstOr

abbrev V := Fin 9
abbrev A := (V → Bool) → Bool

def image : Fin 12 → V → V :=
  ![![0,1,2,3,4,5,6,7,8],
    ![0,5,8,3,4,1,7,6,2],
    ![1,0,5,8,6,2,4,7,3],
    ![1,2,3,8,6,0,7,4,5],
    ![2,1,0,5,7,3,6,4,8],
    ![2,3,8,5,7,1,4,6,0],
    ![3,2,1,0,4,8,7,6,5],
    ![3,8,5,0,4,2,6,7,1],
    ![5,0,1,2,7,8,4,6,3],
    ![5,8,3,2,7,0,6,4,1],
    ![8,3,2,1,6,5,4,7,0],
    ![8,5,0,1,6,3,7,4,2]]

private def inverse : Fin 12 → V → V :=
  ![![0,1,2,3,4,5,6,7,8],
    ![0,5,8,3,4,1,7,6,2],
    ![1,0,5,8,6,2,4,7,3],
    ![5,0,1,2,7,8,4,6,3],
    ![2,1,0,5,7,3,6,4,8],
    ![8,5,0,1,6,3,7,4,2],
    ![3,2,1,0,4,8,7,6,5],
    ![3,8,5,0,4,2,6,7,1],
    ![1,2,3,8,6,0,7,4,5],
    ![5,8,3,2,7,0,6,4,1],
    ![8,3,2,1,6,5,4,7,0],
    ![2,3,8,5,7,1,4,6,0]]

private theorem inverses :
    ∀ k i, inverse k (image k i) = i ∧ image k (inverse k i) = i := by decide

def perm (k : Fin 12) : Equiv.Perm V where
  toFun := image k
  invFun := inverse k
  left_inv i := (inverses k i).1
  right_inv i := (inverses k i).2

def reps : Fin 6 → V × V := ![(0,1), (0,2), (0,3), (0,4), (0,6), (4,6)]

theorem coverage : ∀ i j : V, i ≠ j → ∃ (k : Fin 12) (t : Fin 6),
    (perm k i = (reps t).1 ∧ perm k j = (reps t).2) ∨
    (perm k i = (reps t).2 ∧ perm k j = (reps t).1) := by decide

def edges : List (V × V) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]

def adj (i j : V) : Bool := edges.contains (i,j) || edges.contains (j,i)

theorem preserves_edge : ∀ k i j, adj (perm k i) (perm k j) = adj i j := by decide

def target (x : V → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

private theorem target_edges (x : V → Bool) :
    target x = edges.any (fun e => x e.1 && x e.2) := by
  simp [target, edges, Bool.or_assoc]

private theorem target_iff (x : V → Bool) :
    target x = true ↔ ∃ i j, adj i j = true ∧ x i = true ∧ x j = true := by
  rw [target_edges, List.any_eq_true]
  constructor
  · rintro ⟨⟨i,j⟩, hmem, hxy⟩
    have h : x i = true ∧ x j = true := by simpa using hxy
    exact ⟨i, j, by simp [adj, hmem], h⟩
  · rintro ⟨i,j,he,hx,hy⟩
    simp [adj] at he
    rcases he with h | h
    · exact ⟨(i,j), h, by simp [hx,hy]⟩
    · exact ⟨(j,i), h, by simp [hx,hy]⟩

def rename (k : Fin 12) (f : A) : A := fun x => f (fun i => x (perm k i))

theorem rename_target (k : Fin 12) : rename k target = target := by
  funext x
  change target (fun i => x (perm k i)) = target x
  have h : target (fun i => x (perm k i)) = true ↔ target x = true := by
    rw [target_iff, target_iff]
    constructor
    · rintro ⟨i,j,he,hx,hy⟩
      exact ⟨perm k i, perm k j, (preserves_edge k i j).trans he, hx, hy⟩
    · rintro ⟨i,j,he,hx,hy⟩
      refine ⟨(perm k).symm i, (perm k).symm j, ?_, by simpa, by simpa⟩
      simpa using (preserves_edge k ((perm k).symm i) ((perm k).symm j)).symm.trans (by simpa using he)
  cases hl : target (fun i => x (perm k i)) <;> cases hr : target x <;> simp_all

def raw (i : V) : A := fun x => x i
def canon (f : A) : A := fun x => xor (f x) (f fun _ => false)

def gate (d : Fin 4) (a b : A) : A := fun x =>
  match d.val with
  | 0 => a x && b x
  | 1 => a x && !b x
  | 2 => !a x && b x
  | _ => a x || b x

def swapGate : Fin 4 → Fin 4 := ![0,2,1,3]

theorem rename_raw (k i) : rename k (raw i) = raw (perm k i) := rfl
theorem rename_canon (k f) : rename k (canon f) = canon (rename k f) := rfl
theorem rename_gate (k d a b) : rename k (gate d a b) = gate d (rename k a) (rename k b) := rfl

theorem gate_swap (d) (a b : A) : gate d a b = gate (swapGate d) b a := by
  funext x
  fin_cases d <;> cases ha : a x <;> cases hb : b x <;> simp [gate, swapGate, ha, hb]

-- The output names for the first signed gate are transported as well:
-- swapping the vertices exchanges the two directed choices of polarity.
theorem gate_to_representative (i j : V) (hij : i ≠ j) (d : Fin 4) :
    ∃ (k : Fin 12) (t : Fin 6),
      (rename k (gate d (raw i) (raw j)) = gate d (raw (reps t).1) (raw (reps t).2)) ∨
      (rename k (gate d (raw i) (raw j)) = gate (swapGate d) (raw (reps t).1) (raw (reps t).2)) := by
  obtain ⟨k,t,h | h⟩ := coverage i j hij
  · exact ⟨k,t, Or.inl (by rw [rename_gate, rename_raw, rename_raw, h.1, h.2])⟩
  · exact ⟨k,t, Or.inr (by rw [rename_gate, rename_raw, rename_raw, h.1, h.2, gate_swap])⟩

end FirstOr



noncomputable section CertifiedComponents
local instance truthWireEq : DecidableEq FirstOr.A := Classical.decEq _

namespace Signed
open FirstOr PEqualNP.CircuitLowerBounds
noncomputable section LocalProof1
def zero : A := fun _ => false
def rootW : List A := List.ofFn raw

inductive Live : Nat → Finset A → Prop
  | stop : Live 0 {target}
  | step {k : Nat} {U : Finset A} {a b : A} {d : Fin 4}
      (ha : a ≠ zero) (hb : b ≠ zero) (hab : a ≠ b)
      (fresh : gate d a b ∉ insert a (insert b U))
      (tail : Live k (insert (gate d a b) U)) :
      Live (k+1) (insert a (insert b U))

theorem target_ne : target ≠ zero := by
  intro h
  have e := congrFun h (fun _ => true)
  contradiction

theorem live_ne_zero {k S} (h : Live k S) : ∀ a ∈ S, a ≠ zero := by
  induction h with
  | stop => simpa using target_ne
  | step ha hb hab hf hl ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a hm => ih a (Finset.mem_insert_of_mem hm)⟩

private theorem canon_zero : canon zero = zero := rfl
private theorem canon_one : canon (fun _ => true) = zero := rfl
private theorem canon_not (a : A) : canon (fun x => !a x) = canon a := by
  funext x
  change xor (!(a x)) (!(a (fun _ => false))) = xor (a x) (a (fun _ => false))
  cases a x <;> cases a (fun _ => false) <;> rfl

private theorem norm_and (a b : A) :
    ∃ d : Fin 4, canon (fun x => a x && b x) = gate d (canon a) (canon b) := by
  refine ⟨if a (fun _ => false) then (if b (fun _ => false) then 3 else 2)
    else (if b (fun _ => false) then 1 else 0), ?_⟩
  funext x
  cases ha : a (fun _ => false) <;> cases hb : b (fun _ => false) <;>
    cases hax : a x <;> cases hbx : b x <;> simp [canon,gate,ha,hb,hax,hbx]

private theorem norm_or (a b : A) :
    ∃ d : Fin 4, canon (fun x => a x || b x) = gate d (canon a) (canon b) := by
  refine ⟨if a (fun _ => false) then (if b (fun _ => false) then 0 else 1)
    else (if b (fun _ => false) then 2 else 3), ?_⟩
  funext x
  cases ha : a (fun _ => false) <;> cases hb : b (fun _ => false) <;>
    cases hax : a x <;> cases hbx : b x <;> simp [canon,gate,ha,hb,hax,hbx]

private theorem deg_left (d : Fin 4) (a : A) :
    gate d zero a = zero ∨ gate d zero a = a := by
  fin_cases d
  · left; rfl
  · left; rfl
  · right; rfl
  · right; rfl

private theorem deg_right (d : Fin 4) (a : A) :
    gate d a zero = zero ∨ gate d a zero = a := by
  rw [gate_swap]
  exact deg_left _ _

private theorem deg_same (d : Fin 4) (a : A) :
    gate d a a = zero ∨ gate d a a = a := by
  fin_cases d
  · right; funext x; cases h : a x <;> simp [gate,h]
  · left; funext x; cases h : a x <;> simp [gate,h,zero]
  · left; funext x; cases h : a x <;> simp [gate,h,zero]
  · right; funext x; cases h : a x <;> simp [gate,h]

def Old (w : List A) (z : A) : Prop := z = zero ∨ z ∈ w
def Witness (w : List A) (z : A) : Prop :=
  ∃ d a b, a ∈ w ∧ b ∈ w ∧ a ≠ zero ∧ b ≠ zero ∧ a ≠ b ∧ z = gate d a b

private theorem combine_rep {w a b} (d : Fin 4) (ha : Old w a) (hb : Old w b) :
    Old w (gate d a b) ∨ Witness w (gate d a b) := by
  by_cases az : a = zero
  · subst a
    rcases deg_left d b with e | e
    · exact Or.inl (Or.inl e)
    · exact Or.inl (e.symm ▸ hb)
  by_cases bz : b = zero
  · subst b
    rcases deg_right d a with e | e
    · exact Or.inl (Or.inl e)
    · exact Or.inl (e.symm ▸ ha)
  by_cases same : a = b
  · subst b
    rcases deg_same d a with e | e
    · exact Or.inl (Or.inl e)
    · exact Or.inl (e.symm ▸ ha)
  exact Or.inr ⟨d,a,b,ha.resolve_left az,hb.resolve_left bz,az,bz,same,rfl⟩

def gv (w : List A) (g : Gate) : A :=
  fun x => g.op.eval (g.inputs.map fun i => (w.getD i zero) x)
def execute (gs : List Gate) (w : List A) : List A :=
  gs.foldl (fun l g => l ++ [gv l g]) w
def counted (g : Gate) : Bool := g.op.eval [true]
def Legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private theorem read_old (w : List A) (i : Nat) : Old (w.map canon) (canon (w.getD i zero)) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inl canon_zero
  | some a => exact Or.inr (List.mem_map.mpr ⟨a,List.mem_of_getElem? h,rfl⟩)

private theorem gate_rep (w : List A) (g : Gate) (hl : Legal g) :
    Old (w.map canon) (canon (gv w g)) ∨ (counted g = true ∧ Witness (w.map canon) (canon (gv w g))) := by
  obtain ⟨o,ls⟩ := g
  obtain ⟨ho,hlen⟩ := hl
  change o = .and ∨ o = .or ∨ o = .not at ho
  change ls.length ≤ 2 at hlen
  cases ls with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl (Or.inl canon_one)
    · exact Or.inl (Or.inl canon_zero)
    · exact Or.inl (Or.inl canon_one)
  | cons i ls =>
    cases ls with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · have eq : gv w ⟨.and,[i]⟩ = w.getD i zero := by funext x; simp [gv, GateOp.eval]
        rw [eq]; exact Or.inl (read_old w i)
      · have eq : gv w ⟨.or,[i]⟩ = w.getD i zero := by funext x; simp [gv, GateOp.eval]
        rw [eq]; exact Or.inl (read_old w i)
      · change Old _ (canon (fun x => !(w.getD i zero x))) ∨ _
        rw [canon_not]; exact Or.inl (read_old w i)
    | cons j ls =>
      cases ls with
      | cons t ts => simp at hlen
      | nil =>
        rcases ho with rfl | rfl | rfl
        · have eq : gv w ⟨.and,[i,j]⟩ = fun x => (w.getD i zero x) && (w.getD j zero x) := by
            funext x; simp [gv, GateOp.eval]
          obtain ⟨d,he⟩ := norm_and (w.getD i zero) (w.getD j zero)
          rw [eq,he]
          exact (combine_rep d (read_old w i) (read_old w j)).imp id (fun h => ⟨rfl,h⟩)
        · have eq : gv w ⟨.or,[i,j]⟩ = fun x => (w.getD i zero x) || (w.getD j zero x) := by
            funext x; simp [gv, GateOp.eval]
          obtain ⟨d,he⟩ := norm_or (w.getD i zero) (w.getD j zero)
          rw [eq,he]
          exact (combine_rep d (read_old w i) (read_old w j)).imp id (fun h => ⟨rfl,h⟩)
        · change Old _ (canon (fun x => !(w.getD i zero x))) ∨ _
          rw [canon_not]; exact Or.inl (read_old w i)

private theorem pull_gate {w : List A} {g k S} (hl : Legal g) (live : Live k S)
    (sub : ∀ a ∈ S, a ∈ (w ++ [gv w g]).map canon) :
    ∃ k' S', k' ≤ k + (if counted g then 1 else 0) ∧ Live k' S' ∧ ∀ a ∈ S', a ∈ w.map canon := by
  let z := canon (gv w g)
  have all : ∀ a ∈ S, a ∈ w.map canon ∨ a = z := by simpa [z] using sub
  by_cases hz : z ∈ S
  · by_cases hw : z ∈ w.map canon
    · refine ⟨k,S,by omega,live,?_⟩
      intro a ha; rcases all a ha with h | rfl
      · exact h
      · exact hw
    · rcases gate_rep w g hl with old | ⟨count, d, a, b, am, bm, an, bn, ab, eq⟩
      · rcases old with he | hm
        · exact False.elim (live_ne_zero live _ hz he)
        · exact False.elim (hw hm)
      · change z = gate d a b at eq
        let U := S.erase z
        have hu : ∀ t ∈ U, t ∈ w.map canon := by
          intro t ht
          obtain ⟨ne,hm⟩ := Finset.mem_erase.mp ht
          exact (all t hm).resolve_right ne
        have fresh : z ∉ insert a (insert b U) := by
          intro h
          rcases Finset.mem_insert.mp h with e | hm
          · exact hw (e ▸ am)
          rcases Finset.mem_insert.mp hm with e | hm
          · exact hw (e ▸ bm)
          · exact hw (hu _ hm)
        have tail : Live k (insert z U) := by simpa [U,Finset.insert_erase hz] using live
        rw [eq] at fresh tail
        refine ⟨k+1,_,by simp [count],Live.step an bn ab fresh tail,?_⟩
        simpa only [Finset.forall_mem_insert] using And.intro am (And.intro bm hu)
  · refine ⟨k,S,by omega,live,?_⟩
    intro a ha
    exact (all a ha).resolve_right (fun e => hz (e ▸ ha))

private theorem extract (gs : List Gate) (w : List A)
    (legal : ∀ g ∈ gs, Legal g) (hout : target ∈ (execute gs w).map canon) :
    ∃ k S, k ≤ gs.countP counted ∧ Live k S ∧ ∀ a ∈ S, a ∈ w.map canon := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,hl,hs⟩ := ih (w ++ [gv w g]) (fun t ht => legal t (by simp [ht])) hout
    obtain ⟨k',S',hk',hl',hs'⟩ := pull_gate (legal g (by simp)) hl hs
    exact ⟨k',S',by simpa [List.countP_cons] using le_trans hk' (Nat.add_le_add_right hk _),hl',hs'⟩

private theorem eval_read (w : List A) (x : V → Bool) (i : Nat) :
    (w.map (fun f => f x)).getD i false = (w.getD i zero) x := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases h : w[i]? <;> rfl

private theorem execute_eval (gs : List Gate) (w : List A) (x : V → Bool) :
    (execute gs w).map (fun f => f x) =
      gs.foldl (fun (l : List Bool) g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)])
        (w.map (fun f => f x)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w ++ [gv w g])).map _ = _
    rw [ih]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,gv,eval_read]

theorem circuit_live (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : PEqualNP.MetaComplexity.circuitFun 9 C = target) :
    ∃ k S, k ≤ C.gates.countP counted ∧ Live k S ∧ ∀ a ∈ S, a ∈ rootW := by
  let w := execute C.gates rootW
  have heval (x : V → Bool) : (w.getD C.output zero) x = target x := by
    rw [← eval_read]
    change ((execute C.gates rootW).map _).getD C.output false = _
    rw [execute_eval]
    have initial : rootW.map (fun f => f x) = List.ofFn x := by rw [rootW,List.map_ofFn]; rfl
    rw [initial]
    exact congrFun he x
  have eq : w.getD C.output zero = target := funext heval
  have hit : target ∈ w := by
    simp only [List.getD_eq_getElem?_getD] at eq
    cases e : w[C.output]? with
    | none =>
      rw [e] at eq
      exact False.elim (target_ne eq.symm)
    | some a =>
      rw [e] at eq
      exact eq ▸ List.mem_of_getElem? e
  have ct : canon target = target := by funext x; simp [canon,target]
  have cr (i : V) : canon (raw i) = raw i := by funext x; simp [canon,raw]
  have start : rootW.map canon = rootW := by rw [rootW,List.map_ofFn]; simp only [Function.comp_def,cr]
  obtain ⟨k,S,le,hl,hs⟩ := extract C.gates rootW h (List.mem_map.mpr ⟨target,hit,ct⟩)
  exact ⟨k,S,le,hl,by simpa [start] using hs⟩

end LocalProof1
end Signed

namespace Signed
open FirstOr
noncomputable section LocalProof2
theorem gate_congr_at (d : Fin 4) (a b : A) {x y : V → Bool}
    (ha : a x = a y) (hb : b x = b y) : gate d a b x = gate d a b y := by
  fin_cases d <;> simp [gate, ha, hb]

theorem Live.agree {k S} (run : Live k S) {x y : V → Bool}
    (h : ∀ a ∈ S, a x = a y) : target x = target y := by
  induction run with
  | stop => exact h target (by simp)
  | @step k U a b d ha hb hab fresh tail ih =>
    apply ih
    intro z hz
    rcases Finset.mem_insert.mp hz with hgate | hU
    · subst z
      exact gate_congr_at d a b (h a (by simp)) (h b (by simp))
    · exact h z (by simp [hU])

theorem Live.distinguishes {k S} (run : Live k S) {x y : V → Bool}
    (h : target x ≠ target y) : ∃ a ∈ S, a x ≠ a y := by
  by_contra! hn
  exact h (run.agree hn)

-- When no surviving old wire separates two rows of different target value,
-- the new binary gate must separate those rows.
theorem Live.new_gate_separates {k U a b d} (tail : Live k (insert (gate d a b) U))
    {x y : V → Bool} (h : target x ≠ target y) (hU : ∀ z ∈ U, z x = z y) :
    gate d a b x ≠ gate d a b y := by
  intro hg
  apply h
  apply tail.agree
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact hg
  · exact hU z hz

-- A state with k remaining binary gates has at most k+1 live wires.
-- U may retain either operand.
theorem Live.card_le {k S} (run : Live k S) : S.card ≤ k + 1 := by
  induction run with
  | stop => simp
  | @step k U a b d ha hb hab fresh tail ih =>
    have hnew : gate d a b ∉ U := fun h => fresh (by simp [h])
    simp [hnew] at ih
    have hA := Finset.card_insert_le a (insert b U)
    have hB := Finset.card_insert_le b U
    omega

end LocalProof2
end Signed

namespace Signed

open FirstOr
noncomputable section LocalProof3
open scoped Classical

def originals : Finset A := (List.ofFn raw).toFinset

theorem mem_originals {f : A} : f ∈ originals ↔ ∃ i : V, raw i = f := by
  change f ∈ (List.ofFn raw).toFinset ↔ _
  rw [List.mem_toFinset, List.mem_ofFn]

private def mate : V → V := ![1,0,1,2,3,0,1,2,3]
private def single (i : V) : V → Bool := fun t => decide (t = mate i)
private def switched (i : V) (x : V → Bool) : V → Bool :=
  fun t => if t = i then true else x t

private theorem essential_rows : ∀ i, target (single i) = false ∧
    target (switched i (single i)) = true := by decide

theorem Live.root_eq_of_subset {k S} (run : Live k S) (hS : S ⊆ originals) :
    S = originals := by
  apply Finset.Subset.antisymm hS
  intro f hf
  obtain ⟨i, rfl⟩ := mem_originals.mp hf
  obtain ⟨h0,h1⟩ := essential_rows i
  obtain ⟨z,hz,hn⟩ := run.distinguishes (x := single i) (y := switched i (single i))
    (by rw [h0,h1]; decide)
  obtain ⟨j, rfl⟩ := mem_originals.mp (hS hz)
  have hji : j = i := by
    by_contra hij
    exact hn (by simp [raw, switched, hij])
  simpa [hji] using hz

theorem target_not_original : target ∉ originals := by
  intro hm
  obtain ⟨i, heq⟩ := mem_originals.mp hm
  let x : V → Bool := fun j => decide (j = i)
  have h : ∀ i : V, target (fun j => decide (j = i)) = false := by decide
  have he := congrFun heq x
  change x i = target (fun j => decide (j = i)) at he
  rw [h] at he
  simp [x] at he

private def loMask (v : Bool) : V → V → Nat :=
  if v then
    ![![0,2,20,10,16,32,80,130,258],
      ![1,0,4,9,20,36,64,129,257],
      ![9,2,0,8,18,34,72,128,258],
      ![5,18,4,0,16,36,68,144,256],
      ![1,10,5,8,0,40,65,129,257],
      ![1,130,5,9,144,0,65,128,256],
      ![257,2,260,10,18,34,0,130,256],
      ![5,34,4,40,20,32,68,0,260],
      ![9,10,36,8,48,32,64,136,0]]
  else
    ![![0,16,2,2,2,2,2,2,2],
      ![4,0,1,1,1,1,1,1,1],
      ![2,8,0,2,2,2,2,2,2],
      ![4,4,16,0,4,4,4,4,4],
      ![8,1,1,1,0,1,1,1,1],
      ![128,1,1,1,1,0,1,1,1],
      ![2,256,2,2,2,2,0,2,2],
      ![4,4,32,4,4,4,4,0,4],
      ![8,8,8,32,8,8,8,8,0]]

private def lo (d : Fin 4) (i j : V) : V → Bool :=
  fun t => (loMask (d.val % 2 == 1) i j).testBit t.val

private theorem absorbing_rows : ∀ (i j : V) (d : Fin 4), i ≠ j →
    target (lo d i j) = false ∧ target (switched i (lo d i j)) = true ∧
    gate d (raw i) (raw j) (lo d i j) = gate d (raw i) (raw j) (switched i (lo d i j)) := by
  decide

theorem Live.keep_left {k U} {i j : V} {d : Fin 4} (hij : i ≠ j)
    (run : Live k (insert (gate d (raw i) (raw j)) U)) (hU : U ⊆ originals) :
    raw i ∈ U := by
  by_contra hmissing
  obtain ⟨h0,h1,hgate⟩ := absorbing_rows i j d hij
  apply (run.new_gate_separates (x := lo d i j) (y := switched i (lo d i j))
    (by rw [h0,h1]; decide) ?_) hgate
  intro z hz
  obtain ⟨l,rfl⟩ := mem_originals.mp (hU hz)
  have hli : l ≠ i := fun heq => hmissing (heq ▸ hz)
  simp [raw, switched, hli]

theorem Live.keep_right {k U} {i j : V} {d : Fin 4} (hij : i ≠ j)
    (run : Live k (insert (gate d (raw i) (raw j)) U)) (hU : U ⊆ originals) :
    raw j ∈ U := by
  rw [gate_swap d] at run
  exact run.keep_left hij.symm hU

private theorem rename_injective (k : Fin 12) : Function.Injective (FirstOr.rename k) := by
  intro f g h
  funext x
  have eq := congrFun h (fun v => x ((perm k).symm v))
  simpa [FirstOr.rename] using eq

private def asEmbedding (k : Fin 12) : A ↪ A := ⟨FirstOr.rename k, rename_injective k⟩

theorem Live.relabel {k S} (run : Live k S) (a : Fin 12) :
    Live k (S.map (asEmbedding a)) := by
  induction run with
  | stop => simpa [asEmbedding, rename_target] using Live.stop
  | @step m U p q d hp hq hpq fresh tail ih =>
    let e := asEmbedding a
    have hz : e zero = zero := rfl
    have hp' : e p ≠ zero := fun h => hp (e.injective (h.trans hz.symm))
    have hq' : e q ≠ zero := fun h => hq (e.injective (h.trans hz.symm))
    have hpq' : e p ≠ e q := fun h => hpq (e.injective h)
    have he : e (gate d p q) = gate d (e p) (e q) := rfl
    have hf : e (gate d p q) ∉ (insert p (insert q U)).map e := by simpa using fresh
    simp only [Finset.map_insert, he] at hf
    change Live m ((insert (gate d p q) U).map e) at ih
    change Live (m+1) ((insert p (insert q U)).map e)
    simp only [Finset.map_insert, he] at ih ⊢
    exact Live.step hp' hq' hpq' hf ih

private theorem map_originals (k : Fin 12) : originals.map (asEmbedding k) = originals := by
  ext a
  constructor
  · intro h
    obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp h
    obtain ⟨i,rfl⟩ := mem_originals.mp hz
    exact mem_originals.mpr ⟨perm k i, rfl⟩
  · intro h
    obtain ⟨i,rfl⟩ := mem_originals.mp h
    refine Finset.mem_map.mpr ⟨raw ((perm k).symm i), mem_originals.mpr ⟨_, rfl⟩, ?_⟩
    change raw (perm k ((perm k).symm i)) = raw i
    simp

-- The 24 exact states used by the finite search cover every alleged circuit
-- with at most twelve binary gates. Both operands of its first gate stay live.
theorem Live.first_cases {k S} (run : Live k S) (hk : k ≤ 12) (hsub : S ⊆ originals) :
    ∃ (t : Fin 6) (d : Fin 4) (k' : ℕ), k' ≤ 11 ∧
      Live k' (insert (gate d (raw (reps t).1) (raw (reps t).2)) originals) := by
  have hroot := run.root_eq_of_subset hsub
  cases run with
  | stop =>
    exact False.elim (target_not_original (hsub (by simp)))
  | @step m U a b d ha hb hab fresh tail =>
    have hU : U ⊆ originals := fun z hz => hsub (by simp [hz])
    obtain ⟨i,rfl⟩ := mem_originals.mp (hsub (show a ∈ insert a (insert b U) by simp))
    obtain ⟨j,rfl⟩ := mem_originals.mp (hsub (show b ∈ insert (raw i) (insert b U) by simp))
    have hij : i ≠ j := fun eq => hab (congrArg raw eq)
    have hleft := tail.keep_left hij hU
    have hright := tail.keep_right hij hU
    have hu : U = originals := by simpa [hleft, hright] using hroot
    subst U
    obtain ⟨z,t,ho⟩ := gate_to_representative i j hij d
    have hmap := tail.relabel z
    rw [Finset.map_insert, map_originals] at hmap
    change Live m (insert (FirstOr.rename z (gate d (raw i) (raw j))) originals) at hmap
    rcases ho with ho | ho
    · exact ⟨t,d,m,by omega, ho ▸ hmap⟩
    · exact ⟨t,swapGate d,m,by omega, ho ▸ hmap⟩

end LocalProof3
end Signed


namespace Signed

open FirstOr
open scoped Classical

-- Once the finite search is certified at these 24 states, this is exactly
-- the posted lower bound, including the original count of AND and OR gates.
theorem posted_of_no_first_case
    (none : ∀ (t : Fin 6) (d : Fin 4) (k : ℕ), k ≤ 11 →
      ¬ Live k (insert (gate d (raw (reps t).1) (raw (reps t).2)) originals)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x3 : Fin (9 : ℕ) → Bool) => x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ))) → (13 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4.op.eval [Bool.true]) x1.gates := by
  intro circuit hfanin hfun
  change 13 ≤ circuit.gates.countP counted
  obtain ⟨k,S,hk,hrun,hsub⟩ := circuit_live circuit hfanin hfun
  by_contra! hsmall
  have hs : S ⊆ originals := fun a ha => List.mem_toFinset.mpr (hsub a ha)
  obtain ⟨t,d,k',hk',hcan⟩ := hrun.first_cases (by omega) hs
  exact none t d k' hk' hcan

end Signed

namespace Signed
open FirstOr
noncomputable section LocalProof4

-- A backwards slice of a signed circuit with a selectable output.
inductive LiveFor (goal : A) : Nat → Finset A → Prop where
  | stop : LiveFor goal 0 {goal}
  | step {k U a b} {d : Fin 4} (ha : a ≠ zero) (hb : b ≠ zero) (hab : a ≠ b)
      (fresh : gate d a b ∉ insert a (insert b U))
      (tail : LiveFor goal k (insert (gate d a b) U)) :
      LiveFor goal (k + 1) (insert a (insert b U))

theorem Live.toLiveFor {k S} (r : Live k S) : LiveFor target k S := by
  induction r with
  | stop => exact .stop
  | step ha hb hn hf _ ih => exact .step ha hb hn hf ih

theorem LiveFor.wires_ne {t k S} (r : LiveFor t k S) (ht : t ≠ zero) :
    ∀ a ∈ S, a ≠ zero := by
  induction r with
  | stop => simpa using ht
  | step ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha, hb, fun a hm => ih a (Finset.mem_insert_of_mem hm)⟩

-- The zero and one constant functions have the same normalized signal.  Count
-- original wires here, so distinct wires collapsing to zero still count separately.
def constantWires (f : A → A) (S : Finset A) : Nat := (S.filter (fun a => f a = zero)).card

private theorem constants_insert (f : A → A) (a : A) (U : Finset A) :
    constantWires f (insert a U) =
    if f a = zero ∧ a ∉ U then constantWires f U + 1 else constantWires f U := by
  by_cases h : f a = zero
  · by_cases hm : a ∈ U
    · simp [h, hm]
    · simp [constantWires, Finset.filter_insert, h, hm]
  · simp [constantWires, Finset.filter_insert, h]

private theorem projection_cost (f : A → A) {g a b : A} {U : Finset A}
    (hg : g ∉ U) (hboth : f a = zero → f b = zero → f g = zero) :
    constantWires f (insert a (insert b U)) + (if f a ≠ zero ∧ f b ≠ zero then 1 else 0) ≤
      constantWires f (insert g U) + 1 := by
  simp only [constants_insert]
  by_cases ha : f a = zero <;> by_cases hb : f b = zero <;>
    by_cases hgc : f g = zero <;> by_cases hi : a ∈ insert b U <;>
    by_cases hj : b ∈ U <;> simp_all <;> omega

private theorem pull_projected {goal a b c : A} {d : Fin 4} {n : Nat} {T P : Finset A}
    (ht : goal ≠ zero) (run : LiveFor goal n T) (all : T ⊆ insert c P)
    (am : a ∈ P) (bm : b ∈ P) (eq : c = gate d a b) :
    ∃ m Q, m ≤ n + (if a ≠ zero ∧ b ≠ zero then 1 else 0) ∧
      LiveFor goal m Q ∧ Q ⊆ P := by
  by_cases hc : c ∈ T ∧ c ∉ P
  · obtain ⟨ct, cp⟩ := hc
    have cn : c ≠ zero := run.wires_ne ht c ct
    have an : a ≠ zero := by
      rintro rfl
      rcases deg_left d b with h | h
      · exact cn (eq.trans h)
      · exact cp ((eq.trans h).symm ▸ bm)
    have bn : b ≠ zero := by
      rintro rfl
      rcases deg_right d a with h | h
      · exact cn (eq.trans h)
      · exact cp ((eq.trans h).symm ▸ am)
    have ab : a ≠ b := by
      rintro rfl
      rcases deg_same d a with h | h
      · exact cn (eq.trans h)
      · exact cp ((eq.trans h).symm ▸ am)
    let U := T.erase c
    have uP : U ⊆ P := by
      intro z hz
      obtain ⟨ne, mem⟩ := Finset.mem_erase.mp hz
      exact (Finset.mem_insert.mp (all mem)).resolve_left ne
    have fresh : c ∉ insert a (insert b U) := by
      intro h
      rcases Finset.mem_insert.mp h with rfl | h
      · exact cp am
      rcases Finset.mem_insert.mp h with rfl | h
      · exact cp bm
      · exact cp (uP h)
    have tail : LiveFor goal n (insert c U) := by simpa [U, Finset.insert_erase ct] using run
    rw [eq] at fresh tail
    refine ⟨n+1, _, by simp [an,bn], LiveFor.step an bn ab fresh tail, ?_⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | h
    · exact am
    rcases Finset.mem_insert.mp h with rfl | h
    · exact bm
    · exact uP h
  · refine ⟨n,T,by omega,run,?_⟩
    intro z hz
    rcases Finset.mem_insert.mp (all hz) with rfl | h
    · exact by_contra (fun h => hc ⟨hz,h⟩)
    · exact h

-- A nonconstant restricted goal has a slice shorter by at least the number of
-- currently live wires that become constant. Equal nonconstant images cause no problem.
theorem LiveFor.project_constants {t : A} {k : Nat} {S : Finset A} (run : LiveFor t k S)
    (f : A → A) (hm : ∀ (d : Fin 4) a b, ∃ e, f (gate d a b) = gate e (f a) (f b))
    (ht : f t ≠ zero) :
    ∃ m Q, m + constantWires f S ≤ k ∧ LiveFor (f t) m Q ∧ Q ⊆ S.image f := by
  induction run with
  | stop =>
    refine ⟨0, {f t}, ?_, .stop, ?_⟩
    · simp [constantWires, ht]
    · simp
  | @step k U a b d _ _ _ fresh tail ih =>
    obtain ⟨n,T,hn,run',sub⟩ := ih
    let P := (insert a (insert b U)).image f
    have aP : f a ∈ P := Finset.mem_image_of_mem _ (by simp)
    have bP : f b ∈ P := Finset.mem_image_of_mem _ (by simp)
    let c := f (gate d a b)
    have cover : T ⊆ insert c P := by
      intro z hz
      obtain ⟨w,wm,rfl⟩ := Finset.mem_image.mp (sub hz)
      rcases Finset.mem_insert.mp wm with rfl | wU
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (by simp [wU]))
    obtain ⟨e,eq⟩ := hm d a b
    obtain ⟨m,Q,hcost,proj,hQ⟩ := pull_projected ht run' cover aP bP eq
    have nc : gate d a b ∉ U := fun h => fresh (by simp [h])
    have both : f a = zero → f b = zero → c = zero := by
      intro h1 h2
      rw [show c = gate e (f a) (f b) from eq, h1,h2]
      rcases deg_left e zero with h | h <;> exact h
    have saving := projection_cost f nc both
    exact ⟨m,Q,by omega,proj,hQ⟩

def restrictCanon (ρ : (V → Bool) → V → Bool) (a : A) : A := canon (a ∘ ρ)

theorem restrictCanon_gate (ρ : (V → Bool) → V → Bool) (d : Fin 4) (a b : A) :
    ∃ e, restrictCanon ρ (gate d a b) = gate e (restrictCanon ρ a) (restrictCanon ρ b) := by
  let x₀ : V → Bool := fun _ => false
  let l : Fin 4 := if a (ρ x₀) then ![2,3,0,1] d else d
  let e : Fin 4 := if b (ρ x₀) then ![1,0,3,2] l else l
  refine ⟨e,?_⟩
  funext x
  fin_cases d <;> cases h₀ : a (ρ x₀) <;> cases h₁ : b (ρ x₀) <;>
    cases h₂ : a (ρ x) <;> cases h₃ : b (ρ x) <;>
      simp_all [e,l,restrictCanon,canon,gate,x₀]

theorem Live.cut {k S} (run : Live k S) (ρ : (V → Bool) → V → Bool)
    (ht : restrictCanon ρ target ≠ zero) :
    ∃ m Q, m + constantWires (restrictCanon ρ) S ≤ k ∧
      LiveFor (restrictCanon ρ target) m Q ∧ Q ⊆ S.image (restrictCanon ρ) :=
  run.toLiveFor.project_constants _ (restrictCanon_gate ρ) ht

end LocalProof4
end Signed

namespace Signed
open FirstOr
noncomputable section LocalProof5

def gateCharge (c : A) (bank : Finset A) : Nat := if c = zero ∨ c ∈ bank then 0 else 1

-- Retain the entire sequence of paid gates, including signals no longer needed by its
-- original execution. Either polarity of an earlier signal is already free after normalization.
inductive PaidPrefix (f : A → A) (base : Finset A) : Nat → Finset A → Prop where
  | start : PaidPrefix f base 0 base
  | add {p S a b} {d : Fin 4} (history : PaidPrefix f base p S) (ha : a ∈ S) (hb : b ∈ S) :
      PaidPrefix f base (p + gateCharge (f (gate d a b)) (S.image f)) (insert (gate d a b) S)

private theorem pull_charged {goal a b c : A} {d : Fin 4} {n : Nat} {T P : Finset A}
    (ht : goal ≠ zero) (run : LiveFor goal n T) (all : T ⊆ insert c P)
    (am : a ∈ P) (bm : b ∈ P) (eq : c = gate d a b) :
    ∃ m Q, m ≤ n + gateCharge c P ∧ LiveFor goal m Q ∧ Q ⊆ P := by
  by_cases hc : c = zero ∨ c ∈ P
  · refine ⟨n,T,by simp [gateCharge,hc],run,?_⟩
    intro z hz
    rcases Finset.mem_insert.mp (all hz) with rfl | h
    · exact hc.resolve_left (run.wires_ne ht _ hz)
    · exact h
  · obtain ⟨m,Q,hm,rr,hQ⟩ := pull_projected ht run all am bm eq
    refine ⟨m,Q,?_,rr,hQ⟩
    simp [gateCharge, hc]
    split_ifs at hm <;> omega

theorem PaidPrefix.pull {f : A → A} {base bank : Finset A} {p n : Nat} {Q : Finset A} {goal : A}
    (hist : PaidPrefix f base p bank)
    (hgate : ∀ (d : Fin 4) a b, ∃ e, f (gate d a b) = gate e (f a) (f b))
    (ht : goal ≠ zero) (run : LiveFor goal n Q) (sub : Q ⊆ bank.image f) :
    ∃ m R, m ≤ n + p ∧ LiveFor goal m R ∧ R ⊆ base.image f := by
  induction hist generalizing n Q with
  | start => exact ⟨n,Q,by omega,run,sub⟩
  | @add p S a b d hist am bm ih =>
    rw [Finset.image_insert] at sub
    obtain ⟨e,eq⟩ := hgate d a b
    obtain ⟨n',Q',hn',r',s'⟩ := pull_charged ht run sub
      (Finset.mem_image_of_mem f am) (Finset.mem_image_of_mem f bm) eq
    obtain ⟨m,R,hm,r,s⟩ := ih r' s'
    exact ⟨m,R,by omega,r,s⟩

def LowerFrom (t : A) (bank : Finset A) (lb : Nat) : Prop :=
  ∀ k Q, LiveFor t k Q → Q ⊆ bank → lb ≤ k

-- A checked restricted lower bound certifies rejection whenever it exceeds
-- the cost of the surviving earlier gates plus the suffix, less the live constants.
theorem PaidPrefix.cofactor_bound {base bank active : Finset A} {k p lb : Nat} {t : A}
    (ρ : (V → Bool) → V → Bool) (pref : PaidPrefix (restrictCanon ρ) base p bank)
    (inbank : active ⊆ bank) (run : LiveFor t k active) (ht : restrictCanon ρ t ≠ zero)
    (bound : LowerFrom (restrictCanon ρ t) (base.image (restrictCanon ρ)) lb) :
    lb + constantWires (restrictCanon ρ) active ≤ k + p := by
  obtain ⟨n,Q,hn,rr,s⟩ := run.project_constants _ (restrictCanon_gate ρ) ht
  have sq : Q ⊆ bank.image (restrictCanon ρ) := s.trans (Finset.image_mono _ inbank)
  obtain ⟨m,R,hm,run',s'⟩ := pref.pull (restrictCanon_gate ρ) ht rr sq
  have bound' := bound m R run' s'
  omega

end LocalProof5
end Signed

namespace Signed
open FirstOr
noncomputable section LocalProof6

theorem LiveFor.agrees {t k S} (run : LiveFor t k S) {x y : V → Bool}
    (h : ∀ a ∈ S, a x = a y) : t x = t y := by
  induction run with
  | stop => exact h _ (by simp)
  | @step k U a b d _ _ _ _ _ ih =>
    apply ih
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact gate_congr_at d a b (h _ (by simp)) (h _ (by simp))
    · exact h _ (by simp [hz])

theorem LiveFor.length_bound {t k S} (run : LiveFor t k S) : S.card ≤ k+1 := by
  induction run with
  | stop => simp
  | @step k U a b d ha hb hab fresh tail ih =>
    have hn : gate d a b ∉ U := fun h => fresh (by simp [h])
    simp [hn] at ih
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    omega

-- Removing this wire makes a pair of different outputs indistinguishable.
def EssentialWire (t : A) (bank : Finset A) (wire : A) : Prop :=
  ∃ x y, t x ≠ t y ∧ ∀ b ∈ bank, b ≠ wire → b x = b y

theorem LiveFor.requires {t k Q bank a} (run : LiveFor t k Q) (sub : Q ⊆ bank)
    (essential : EssentialWire t bank a) : a ∈ Q := by
  obtain ⟨x,y,diff,agree⟩ := essential
  by_contra ha
  exact diff (run.agrees (fun w hw => agree w (sub hw) (fun eq => ha (eq ▸ hw))))

theorem LowerFrom.transfer {t g : A} {bank small forced : Finset A} {lb : Nat}
    (bound : LowerFrom g small lb) (ρ : (V → Bool) → V → Bool)
    (goal : restrictCanon ρ t = g) (nz : g ≠ zero)
    (wires : ∀ a ∈ bank, restrictCanon ρ a = zero ∨ restrictCanon ρ a ∈ small)
    (need : ∀ a ∈ forced, EssentialWire t bank a)
    (vanish : ∀ a ∈ forced, restrictCanon ρ a = zero) :
    LowerFrom t bank (lb + forced.card) := by
  intro k Q run sub
  have nz' : restrictCanon ρ t ≠ zero := by simpa only [goal] using nz
  obtain ⟨m,R,hs,r',s'⟩ := run.project_constants _ (restrictCanon_gate ρ) nz'
  rw [goal] at r'
  have rsmall : R ⊆ small := by
    intro a ha
    obtain ⟨b,hm,rfl⟩ := Finset.mem_image.mp (s' ha)
    exact (wires b (sub hm)).resolve_left (r'.wires_ne nz _ ha)
  have forced_in : forced ⊆ Q.filter (fun a => restrictCanon ρ a = zero) := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨run.requires sub (need a ha),vanish a ha⟩
  have nc : forced.card ≤ constantWires (restrictCanon ρ) Q := Finset.card_le_card forced_in
  have lower := bound m R r' rsmall
  omega

theorem LowerFrom.rename_or_drop {t g : A} {bank small : Finset A} {lb : Nat}
    (bound : LowerFrom g small lb) (ρ : (V → Bool) → V → Bool)
    (goal : restrictCanon ρ t = g) (nz : g ≠ zero)
    (wires : ∀ a ∈ bank, restrictCanon ρ a = zero ∨ restrictCanon ρ a ∈ small) :
    LowerFrom t bank lb := by
  simpa using bound.transfer (forced := ∅) ρ goal nz wires (by simp) (by simp)

def Depends (t : A) (i : V) : Prop :=
  ∃ x y, t x ≠ t y ∧ ∀ j, j ≠ i → x j = y j

def rawBank (I : Finset V) : Finset A := I.image raw

theorem raw_injective : Function.Injective raw := by
  intro i j heq
  have e := congrFun heq (fun h => decide (h=i))
  by_contra ne
  simpa [raw,Ne.symm ne] using e

theorem rawBank_size (I : Finset V) : (rawBank I).card = I.card :=
  Finset.card_image_of_injective _ raw_injective

theorem depends_essential {t : A} {bank : Finset A} {i : V} (d : Depends t i)
    (base : bank ⊆ insert zero originals) : EssentialWire t bank (raw i) := by
  obtain ⟨x,y,dd,h⟩ := d
  refine ⟨x,y,dd,?_⟩
  intro w hw hi
  rcases Finset.mem_insert.mp (base hw) with rfl | hmem
  · rfl
  obtain ⟨j,rfl⟩ := mem_originals.mp hmem
  exact h j (fun e => hi (congrArg raw e))

theorem rawBank_subset (I : Finset V) : rawBank I ⊆ insert zero originals := by
  intro a ha
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
  exact Finset.mem_insert_of_mem (mem_originals.mpr ⟨i,rfl⟩)

-- Use one lower bound after deleting, identifying or reordering inputs; each
-- essential coordinate fixed by the same substitution adds one paid gate.
theorem LowerFrom.transfer_inputs {t g : A} {bank small : Finset A} {I : Finset V} {lb : Nat}
    (bound : LowerFrom g small lb) (ρ : (V → Bool) → V → Bool)
    (goal : restrictCanon ρ t = g) (nz : g ≠ zero)
    (base : bank ⊆ insert zero originals)
    (wires : ∀ a ∈ bank, restrictCanon ρ a = zero ∨ restrictCanon ρ a ∈ small)
    (need : ∀ i ∈ I, Depends t i) (vanish : ∀ i ∈ I, restrictCanon ρ (raw i) = zero) :
    LowerFrom t bank (lb + I.card) := by
  rw [← rawBank_size I]
  apply bound.transfer ρ goal nz wires
  · intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    exact depends_essential (need i hi) base
  · intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    exact vanish i hi

theorem support_lower {t : A} {bank : Finset A} (I : Finset V)
    (base : bank ⊆ insert zero originals) (deps : ∀ i ∈ I, Depends t i) :
    LowerFrom t bank (I.card - 1) := by
  intro k Q run sub
  have subset : rawBank I ⊆ Q := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    exact run.requires sub (depends_essential (deps i hi) base)
  have card := Finset.card_le_card subset
  rw [rawBank_size] at card
  have := run.length_bound
  omega

end LocalProof6
end Signed

namespace Signed
open FirstOr
noncomputable section LocalProof7

def clearInputs (I : Finset V) (x : V → Bool) (j : V) : Bool := if j ∈ I then false else x j
def anyInput (I : Finset V) (x : V → Bool) : Bool := decide (∃ i ∈ I, x i = true)
def addLiterals (I : Finset V) (g : A) : A := fun x => anyInput I x || g x

private theorem clear_all_false (I : Finset V) :
    clearInputs I (fun _ => false) = (fun _ => false) := by
  funext j; simp [clearInputs]

private theorem any_cleared (I : Finset V) (x : V → Bool) :
    anyInput I (clearInputs I x) = false := by
  simp only [anyInput,decide_eq_false_iff_not]
  rintro ⟨i,hi,h⟩
  simp [clearInputs,hi] at h

private theorem cleared_var {I : Finset V} {i : V} (hi : i ∈ I) :
    restrictCanon (clearInputs I) (raw i) = zero := by
  funext x; simp [restrictCanon,canon,raw,clearInputs,hi,zero]

private theorem kept_var {I : Finset V} {i : V} (hi : i ∉ I) :
    restrictCanon (clearInputs I) (raw i) = raw i := by
  funext x; simp [restrictCanon,canon,raw,clearInputs,hi]

theorem addLiterals_depends {I : Finset V} {g : A} (hzero : g (fun _ => false) = false)
    {i : V} (hi : i ∈ I) : Depends (addLiterals I g) i := by
  let unit : V → Bool := fun j => decide (j = i)
  have yes : anyInput I unit = true := by
    apply decide_eq_true
    exact ⟨i,hi,by simp [unit]⟩
  have no : anyInput I (fun _ => false) = false := by simp [anyInput]
  refine ⟨(fun _ => false),unit,?_,?_⟩
  · simp [addLiterals,no,yes,hzero]
  · intro j h
    simp [unit,h]

-- Turning all the new, disjoint literal inputs off recovers the original
-- nonconstant target; each new input costs at least one more binary gate.
theorem LowerFrom.or_fresh {g : A} {J : Finset V} {lb : Nat} (bound : LowerFrom g (rawBank J) lb)
    (I : Finset V) (nz : g ≠ zero) (norm : g (fun _ => false) = false)
    (indep : ∀ x, g (clearInputs I x) = g x) :
    LowerFrom (addLiterals I g) (rawBank (I ∪ J)) (lb + I.card) := by
  apply bound.transfer_inputs (clearInputs I) _ nz (rawBank_subset _) _ _ _
  · funext x
    change xor (anyInput I (clearInputs I x) || g (clearInputs I x))
      (anyInput I (clearInputs I (fun _ => false)) || g (clearInputs I (fun _ => false))) = g x
    simp [any_cleared,indep,norm]
  · intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    by_cases hin : i ∈ I
    · exact Or.inl (cleared_var hin)
    · exact Or.inr (by
        rw [kept_var hin]
        exact Finset.mem_image_of_mem _ ((Finset.mem_union.mp hi).resolve_left hin))
  · exact fun _ hi => addLiterals_depends norm hi
  · exact fun _ hi => cleared_var hi

theorem only_literals_lower (I : Finset V) :
    LowerFrom (anyInput I) (rawBank I) (I.card - 1) := by
  apply support_lower I (rawBank_subset I)
  intro i hi
  have h := addLiterals_depends (g := zero) (by rfl) hi
  have eq : addLiterals I zero = anyInput I := by funext x; simp [addLiterals,zero]
  rwa [eq] at h

end LocalProof7
end Signed

namespace Signed
open FirstOr
noncomputable section LocalProof8

-- Delete the two selected positions in increasing list order. This
-- definition works even when later projection makes distinct wire values equal.
def remainingWires {α : Type} (xs : List α) (i j : Fin xs.length) : List α :=
  ((List.ofFn (fun k : Fin xs.length => k)).filter (fun k => decide (k ≠ i ∧ k ≠ j))).map xs.get

def retainWire {α : Type} (keep : Bool) (a : α) (xs : List α) : List α :=
  if keep then a :: xs else xs

def wireStep (xs : List A) (i j : Fin xs.length) (d : Fin 4) (ki kj : Bool) : List A :=
  let a := xs.get i
  let b := xs.get j
  gate d a b :: retainWire ki a (retainWire kj b (remainingWires xs i j))

private theorem mem_remaining {α : Type} (xs : List α) (i j : Fin xs.length) (a : α) :
    a ∈ remainingWires xs i j ↔ ∃ k : Fin xs.length, k ≠ i ∧ k ≠ j ∧ xs.get k = a := by
  simp [remainingWires,List.mem_map,List.mem_filter,List.mem_ofFn,and_assoc]

theorem remaining_iff {xs : List A} (nd : xs.Nodup) (i j : Fin xs.length) (a : A) :
    a ∈ remainingWires xs i j ↔ a ∈ xs ∧ a ≠ xs.get i ∧ a ≠ xs.get j := by
  rw [mem_remaining]
  constructor
  · rintro ⟨k,ni,nj,rfl⟩
    exact ⟨List.mem_iff_get.mpr ⟨k,rfl⟩,fun e => ni (nd.get_inj_iff.mp e),
      fun e => nj (nd.get_inj_iff.mp e)⟩
  · rintro ⟨ha,ni,nj⟩
    obtain ⟨k,rfl⟩ := List.mem_iff_get.mp ha
    exact ⟨k,fun e => ni (congrArg xs.get e),fun e => nj (congrArg xs.get e),rfl⟩

private theorem remaining_nodup {xs : List A} (nd : xs.Nodup) (i j : Fin xs.length) :
    (remainingWires xs i j).Nodup := by
  have all : (List.ofFn (fun k : Fin xs.length => k)).Nodup := List.nodup_ofFn.mpr (fun _ _ h => h)
  apply List.Nodup.map (List.nodup_iff_injective_get.mp nd)
  exact all.filter _

theorem retain_iff {α : Type} (b : Bool) (a x : α) (xs : List α) :
    x ∈ retainWire b a xs ↔ (b = true ∧ x = a) ∨ x ∈ xs := by
  cases b <;> simp [retainWire]

theorem retained_state {n : Nat} {t : A} {U : Finset A} {a b : A} {d : Fin 4}
    (run : LiveFor t n (insert (gate d a b) U)) (xs : List A) (nd : xs.Nodup)
    (parent : xs.toFinset = insert a (insert b U)) (i j : Fin xs.length)
    (ai : xs.get i = a) (bj : xs.get j = b) :
    LiveFor t n (wireStep xs i j d (decide (a ∈ U)) (decide (b ∈ U))).toFinset := by
  have rest_eq : (retainWire (decide (a ∈ U)) (xs.get i)
      (retainWire (decide (b ∈ U)) (xs.get j) (remainingWires xs i j))).toFinset = U := by
    ext w
    have memp : w ∈ xs ↔ w = a ∨ w = b ∨ w ∈ U := by
      have r := Finset.ext_iff.mp parent w
      simpa only [List.mem_toFinset,Finset.mem_insert] using r
    simp only [List.mem_toFinset,retain_iff,remaining_iff nd,ai,bj,memp,decide_eq_true_eq]
    by_cases ha : w = a <;> by_cases hb : w = b <;> simp_all
  rw [ai,bj] at rest_eq
  simpa only [wireStep,List.toFinset_cons,ai,bj,rest_eq] using run

theorem wireStep_nodup {xs : List A} (nd : xs.Nodup) {i j : Fin xs.length} (ij : i ≠ j)
    (d : Fin 4) (ki kj : Bool) (fresh : gate d (xs.get i) (xs.get j) ∉ xs) :
    (wireStep xs i j d ki kj).Nodup := by
  let a := xs.get i
  let b := xs.get j
  let rest := remainingWires xs i j
  have rd : rest.Nodup := remaining_nodup nd _ _
  have ar : a ∉ rest := by simp [a,rest,remaining_iff nd]
  have br : b ∉ rest := by simp [b,rest,remaining_iff nd]
  have ab : a ≠ b := fun h => ij (nd.get_inj_iff.mp h)
  have am : a ∈ xs := List.mem_iff_get.mpr ⟨i,rfl⟩
  have bm : b ∈ xs := List.mem_iff_get.mpr ⟨j,rfl⟩
  have ga : gate d a b ≠ a := fun h => fresh (h.symm ▸ am)
  have gb : gate d a b ≠ b := fun h => fresh (h.symm ▸ bm)
  have gr : gate d a b ∉ rest := fun h => fresh ((remaining_iff nd i j _).mp h).1
  change (gate d a b :: retainWire ki a (retainWire kj b rest)).Nodup
  cases ki <;> cases kj <;> simp [retainWire,rd,ar,br,ab,ga,gb,gr]

-- Every nonterminal exact live state has one of these children with exactly
-- one fewer paid gate; positions refer to the parent list before any projection.
theorem LiveFor.list_step {t : A} {k : Nat} {S : Finset A} (run : LiveFor t k S)
    (xs : List A) (hs : xs.toFinset = S) (nd : xs.Nodup) (out : t ∉ xs) :
    ∃ (n : Nat) (i j : Fin xs.length) (d : Fin 4) (ki kj : Bool), k = n+1 ∧
      i ≠ j ∧ xs.get i ≠ zero ∧ xs.get j ≠ zero ∧ gate d (xs.get i) (xs.get j) ∉ xs ∧
      (wireStep xs i j d ki kj).Nodup ∧ LiveFor t n (wireStep xs i j d ki kj).toFinset := by
  cases run with
  | stop =>
    have ht : t ∈ xs.toFinset := by rw [hs]; simp
    exact False.elim (out (List.mem_toFinset.mp ht))
  | @step n U a b d an bn ab fresh tail =>
    have am : a ∈ xs.toFinset := by rw [hs]; simp
    have bm : b ∈ xs.toFinset := by rw [hs]; simp
    obtain ⟨i,ai⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp am)
    obtain ⟨j,bj⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp bm)
    have ij : i ≠ j := fun e => ab (ai.symm.trans ((congrArg xs.get e).trans bj))
    have fr : gate d (xs.get i) (xs.get j) ∉ xs := by
      intro h
      have mem := List.mem_toFinset.mpr h
      rw [hs,ai,bj] at mem
      exact fresh mem
    refine ⟨n,i,j,d,decide (a∈U),decide (b∈U),rfl,ij,ai ▸ an,bj ▸ bn,fr,
      wireStep_nodup nd ij _ _ _ fr,?_⟩
    exact retained_state tail xs nd hs i j ai bj

theorem LiveFor.raw_start {t : A} {k : Nat} {Q : Finset A} (run : LiveFor t k Q)
    (I : Finset V) (sub : Q ⊆ rawBank I) (deps : ∀ i ∈ I, Depends t i) : Q = rawBank I := by
  apply Finset.Subset.antisymm sub
  intro w hw
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
  exact run.requires sub (depends_essential (deps _ hi) (rawBank_subset I))

end LocalProof8
end Signed

namespace Signed
open FirstOr
noncomputable section LocalProof9

def thetaRemoved : Finset V := {0,4}
def thetaMap : A → A := restrictCanon (clearInputs thetaRemoved)
def thetaGoal : A := thetaMap target
def thetaBank : Finset A := originals.image thetaMap
def ThetaTen : Prop := LowerFrom thetaGoal thetaBank 10

-- Three internally disjoint paths between vertices 2 and 8:
-- 2-3-8, 2-1-6-8, and 2-7-5-8.
theorem theta_edges (x : V → Bool) : thetaGoal x =
    (x 1 && x 2 || x 2 && x 3 || x 1 && x 6 || x 2 && x 7 ||
     x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
  simp [thetaGoal,thetaMap,restrictCanon,canon,target,clearInputs,thetaRemoved]

theorem theta_nonzero : thetaGoal ≠ zero := by
  intro h
  have e := congrFun h (fun _ => true)
  rw [theta_edges] at e
  contradiction

private theorem theta_root (i : V) : thetaMap (raw i) ∈ thetaBank :=
  Finset.mem_image_of_mem _ (mem_originals.mpr ⟨i,rfl⟩)

private theorem theta_input_zero (i : V) (hi : i ∈ thetaRemoved) : thetaMap (raw i) = zero :=
  cleared_var hi

private theorem theta_first_in_bank (z j : V) (d : Fin 4) (hz : z ∈ thetaRemoved) :
    thetaMap (gate d (raw z) (raw j)) ∈ thetaBank := by
  obtain ⟨e,eq⟩ := restrictCanon_gate (clearInputs thetaRemoved) d (raw z) (raw j)
  change thetaMap (gate d (raw z) (raw j)) = gate e (thetaMap (raw z)) (thetaMap (raw j)) at eq
  rw [theta_input_zero z hz] at eq
  rcases deg_left e (thetaMap (raw j)) with h | h
  · rw [eq,h,← theta_input_zero z hz]
    exact theta_root z
  · simpa only [eq,h] using theta_root j

theorem no_first_of_theta (lower : ThetaTen) (z j : V) (hz : z ∈ thetaRemoved)
    (d : Fin 4) {k : Nat} (hk : k ≤ 11) :
    ¬ Live k (insert (gate d (raw z) (raw j)) originals) := by
  intro run
  let state := insert (gate d (raw z) (raw j)) originals
  obtain ⟨m,Q,cost,r,sub⟩ := run.cut (clearInputs thetaRemoved) theta_nonzero
  change m + constantWires thetaMap state ≤ k at cost
  have vanished : rawBank thetaRemoved ⊆ state.filter (fun a => thetaMap a = zero) := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem (mem_originals.mpr ⟨i,rfl⟩),theta_input_zero i hi⟩
  have two : 2 ≤ constantWires thetaMap state := by
    have b := Finset.card_le_card vanished
    rw [rawBank_size] at b
    have hsize : thetaRemoved.card = 2 := by decide
    exact hsize ▸ b
  have bank : state.image thetaMap = thetaBank := by
    change (insert (gate d (raw z) (raw j)) originals).image thetaMap = thetaBank
    rw [Finset.image_insert]
    exact Finset.insert_eq_of_mem (theta_first_in_bank z j d hz)
  change Q ⊆ state.image thetaMap at sub
  have bound := lower m Q r (bank ▸ sub)
  omega

theorem no_first_of_theta10 (h : ThetaTen) : ∀ (t : Fin 6) (d : Fin 4) (k : Nat), k ≤ 11 →
    ¬ Live k (insert (gate d (raw (reps t).1) (raw (reps t).2)) originals) := by
  have hit : ∀ t : Fin 6, (reps t).1 ∈ thetaRemoved := by decide
  exact fun t d _ hk => no_first_of_theta h _ _ (hit t) d hk

end LocalProof9
end Signed


namespace Signed

theorem posted_of_theta10 (h : ThetaTen) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x3 : Fin (9 : ℕ) → Bool) => x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ))) → (13 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4.op.eval [Bool.true]) x1.gates :=
  posted_of_no_first_case (no_first_of_theta10 h)

end Signed
namespace Signed
open FirstOr
noncomputable section LocalProof10

def thetaV : Finset V := {1,2,3,5,6,7,8}
def thetaRoots : Finset A := rawBank thetaV

theorem thetaBank_roots : thetaBank ⊆ insert zero thetaRoots := by
  intro a ha
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨i,rfl⟩ := mem_originals.mp hw
  by_cases hi : i ∈ thetaRemoved
  · rw [theta_input_zero i hi]; simp
  · have covered : ∀ j : V, j ∉ thetaRemoved → j ∈ thetaV := by decide
    change restrictCanon (clearInputs thetaRemoved) (raw i) ∈ insert zero thetaRoots
    rw [kept_var hi]
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (covered i hi))

private def thetaMate : V → V := ![0,2,1,2,4,7,1,2,3]
private def setTrue (i : V) (x : V → Bool) (j : V) : Bool := if j = i then true else x j
private def oneVertex (i j : V) : Bool := decide (j = thetaMate i)

theorem theta_depends (i : V) (hi : i ∈ thetaV) : Depends thetaGoal i := by
  have checked : ∀ j ∈ thetaV, thetaGoal (oneVertex j) ≠ thetaGoal (setTrue j (oneVertex j)) := by decide
  exact ⟨_,_,checked _ hi,fun j hj => by simp [setTrue,hj]⟩

private def thetaMask (top : Bool) : V → V → Nat :=
  if top then ![![0,0,0,0,0,0,0,0,0],
       ![0,0,4,72,0,36,64,192,260],
       ![0,2,0,8,0,34,72,128,258],
       ![0,258,4,0,0,36,68,384,256],
       ![0,0,0,0,0,0,0,0,0],
       ![0,130,260,136,0,0,192,128,256],
       ![0,2,260,10,0,34,0,130,256],
       ![0,34,4,40,0,32,68,0,260],
       ![0,10,36,8,0,32,64,136,0]]
  else ![![0,0,0,0,0,0,0,0,0],
       ![0,0,64,4,0,4,4,4,4],
       ![0,8,0,2,0,2,2,2,2],
       ![0,4,256,0,0,4,4,4,4],
       ![0,0,0,0,0,0,0,0,0],
       ![0,128,128,128,0,0,128,256,128],
       ![0,256,2,2,0,2,0,2,2],
       ![0,4,32,4,0,4,4,0,4],
       ![0,8,8,32,0,8,8,8,0]]

private def thetaWitness (d : Fin 4) (i j : V) : V → Bool :=
  fun a => (thetaMask (d.val % 2 == 1) i j).testBit a.val

private theorem theta_flip : ∀ (i j : V) (d : Fin 4), i ∈ thetaV → j ∈ thetaV → i ≠ j →
    let x := thetaWitness d i j
    thetaGoal x ≠ thetaGoal (setTrue i x) ∧
    gate d (raw i) (raw j) x = gate d (raw i) (raw j) (setTrue i x) := by decide

theorem keep_theta_operand {k : Nat} {U : Finset A} {i j : V} {d : Fin 4}
    (run : LiveFor thetaGoal k (insert (gate d (raw i) (raw j)) U))
    (hi : i ∈ thetaV) (hj : j ∈ thetaV) (ij : i ≠ j) (sub : U ⊆ thetaRoots) :
    raw i ∈ U := by
  by_contra hm
  obtain ⟨different,common⟩ := theta_flip i j d hi hj ij
  apply different
  apply run.agrees
  intro a ha
  rcases Finset.mem_insert.mp ha with rfl | hU
  · exact common
  obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp (sub hU)
  have li : l ≠ i := fun eq => hm (eq ▸ hU)
  simp [raw,setTrue,li]

theorem theta_start {k Q} (run : LiveFor thetaGoal k Q) (sub : Q ⊆ thetaBank) : Q = thetaRoots := by
  have real : Q ⊆ thetaRoots := by
    intro a ha
    exact (Finset.mem_insert.mp (thetaBank_roots (sub ha))).resolve_left (run.wires_ne theta_nonzero _ ha)
  apply Finset.Subset.antisymm real
  intro a ha
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
  exact run.requires real (depends_essential (theta_depends i hi) (rawBank_subset thetaV))

end LocalProof10
end Signed

namespace Signed
open FirstOr
noncomputable section LocalProof11

def cycleFive (x : V → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0

def cycleSix (x : V → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 5 || x 5 && x 0

def cycleBank (n : Nat) : Finset A := rawBank (Finset.univ.filter fun i : V => i.val < n)
def FiveAtLeastSeven : Prop := LowerFrom cycleFive (cycleBank 5) 7
def SixAtLeastEight : Prop := LowerFrom cycleSix (cycleBank 6) 8
def EndpointsExcluded : Prop := ∀ (d : Fin 4) (k : Nat), k ≤ 8 →
  ¬ LiveFor thetaGoal k (insert (gate d (raw 2) (raw 8)) thetaRoots)

private def omitV : Fin 3 → Finset V := ![{3},{1,6},{5,7}]
private def cycleN (r : Fin 3) : Nat := if r = 0 then 6 else 5
private def cycleLB (r : Fin 3) : Nat := if r = 0 then 8 else 7
private def ring (r : Fin 3) : A := if r = 0 then cycleSix else cycleFive

-- Each row sends a surviving old coordinate to its position around the cycle;
-- 9 denotes a coordinate fixed to zero.
private def cycleCode : Fin 3 → V → Nat :=
  ![![9,1,0,9,9,4,2,5,3],
    ![9,9,0,1,9,3,9,4,2],
    ![9,4,0,1,9,9,3,9,2]]
private def cycleInputs (r : Fin 3) (x : V → Bool) (i : V) : Bool :=
  if h : cycleCode r i < 9 then x ⟨cycleCode r i,h⟩ else false
private def projectRing (r : Fin 3) := restrictCanon (cycleInputs r)

private theorem project_ring_goal (r : Fin 3) : projectRing r thetaGoal = ring r := by
  funext x
  fin_cases r <;> simp [projectRing,restrictCanon,canon,theta_edges,ring,cycleInputs,cycleCode,cycleSix,
    cycleFive,Bool.and_comm,Bool.or_comm,Bool.or_left_comm,Bool.or_assoc]
  all_goals rw [Bool.and_comm (x 1) (x 0)]

private theorem ring_ne (r : Fin 3) : ring r ≠ zero := by
  intro eq
  have h := congrFun eq (fun _ => true)
  fin_cases r <;> contradiction

private theorem ring_raw_zero (r : Fin 3) (i : V) (h : ¬ cycleCode r i < 9) :
    projectRing r (raw i) = zero := by
  funext x; simp [projectRing,restrictCanon,canon,raw,cycleInputs,h,zero]

private theorem ring_raw_ok (r : Fin 3) (i : V) :
    projectRing r (raw i) = zero ∨ projectRing r (raw i) ∈ cycleBank (cycleN r) := by
  by_cases h : cycleCode r i < 9
  · right
    let j : V := ⟨cycleCode r i,h⟩
    have eq : projectRing r (raw i) = raw j := by
      funext x; simp [projectRing,restrictCanon,canon,raw,cycleInputs,h,j]
    rw [eq]
    apply Finset.mem_image_of_mem
    have ok : ∀ r i, cycleCode r i < 9 → cycleCode r i < cycleN r := by decide
    simpa [j] using ok r i h
  · exact Or.inl (ring_raw_zero _ _ h)

private theorem omitted_zero (r : Fin 3) (i : V) (hi : i ∈ omitV r) : projectRing r (raw i) = zero := by
  have yes : ∀ r i, i ∈ omitV r → ¬ cycleCode r i < 9 := by decide
  exact ring_raw_zero r i (yes r i hi)

private theorem low_degree_first (h5 : FiveAtLeastSeven) (h6 : SixAtLeastEight) (r : Fin 3)
    (i j : V) (hr : i ∈ omitV r) (d : Fin 4) {k : Nat} (hk : k ≤ 8) :
    ¬ LiveFor thetaGoal k (insert (gate d (raw i) (raw j)) thetaRoots) := by
  intro run
  let state := insert (gate d (raw i) (raw j)) thetaRoots
  have nz : projectRing r thetaGoal ≠ zero := project_ring_goal r ▸ ring_ne r
  obtain ⟨m,Q,cost,rr,sub⟩ := run.project_constants (projectRing r) (restrictCanon_gate _) nz
  rw [project_ring_goal] at rr
  have new_gate : projectRing r (gate d (raw i) (raw j)) = zero ∨
      projectRing r (gate d (raw i) (raw j)) ∈ cycleBank (cycleN r) := by
    obtain ⟨e,eq⟩ := restrictCanon_gate (cycleInputs r) d (raw i) (raw j)
    change projectRing r (gate d (raw i) (raw j)) = gate e (projectRing r (raw i)) (projectRing r (raw j)) at eq
    rw [omitted_zero r i hr] at eq
    rcases deg_left e (projectRing r (raw j)) with h | h
    · exact Or.inl (eq.trans h)
    · rw [eq,h]
      exact ring_raw_ok _ _
  have inbank : Q ⊆ cycleBank (cycleN r) := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp (sub ha)
    have nn := rr.wires_ne (ring_ne r) _ ha
    rcases Finset.mem_insert.mp hv with rfl | h
    · exact new_gate.resolve_left nn
    · obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp h
      exact (ring_raw_ok r v).resolve_left nn
  have known : LowerFrom (ring r) (cycleBank (cycleN r)) (cycleLB r) := by
    fin_cases r
    · exact h6
    · exact h5
    · exact h5
  have needed := known m Q rr inbank
  have saved : rawBank (omitV r) ⊆ state.filter (fun a => projectRing r a = zero) := by
    have inside : ∀ r, omitV r ⊆ thetaV := by decide
    intro a ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem ?_,omitted_zero r z hz⟩
    exact Finset.mem_image_of_mem _ (inside r hz)
  have nc : (omitV r).card ≤ constantWires (projectRing r) state := by
    rw [← rawBank_size]
    exact Finset.card_le_card saved
  have total : ∀ r, cycleLB r + (omitV r).card = 9 := by decide
  change m + constantWires (projectRing r) state ≤ k at cost
  have sum := total r
  omega

theorem theta_of_cycles (h5 : FiveAtLeastSeven) (h6 : SixAtLeastEight) (endpts : EndpointsExcluded) :
    ThetaTen := by
  intro k Q run sub
  have parent := theta_start run sub
  by_contra! hsmall
  cases run with
  | stop =>
    have card := congrArg Finset.card parent
    have seven : thetaRoots.card = 7 := (rawBank_size thetaV).trans (by decide)
    simp [seven] at card
  | @step n U a b d ha hb ab fresh tail =>
    have su : U ⊆ thetaRoots := by intro v hv; rw [← parent]; simp [hv]
    have am : a ∈ thetaRoots := by rw [← parent]; simp
    have bm : b ∈ thetaRoots := by rw [← parent]; simp
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp am
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp bm
    have ij : i ≠ j := fun e => ab (congrArg raw e)
    have left := keep_theta_operand tail hi hj ij su
    have rev := tail
    rw [gate_swap d] at rev
    have right := keep_theta_operand rev hj hi ij.symm su
    have full : U = thetaRoots := by simpa [left,right] using parent
    subst U
    have cases' : ∀ i j : V, i ∈ thetaV → j ∈ thetaV → i ≠ j →
        (∃ r, i ∈ omitV r) ∨ (∃ r,j ∈ omitV r) ∨ (i=2 ∧ j=8) ∨ (i=8 ∧ j=2) := by decide
    have hn : n ≤ 8 := by omega
    rcases cases' i j hi hj ij with ⟨r,hr⟩ | ⟨r,hr⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact low_degree_first h5 h6 r i j hr d hn tail
    · exact low_degree_first h5 h6 r j i hr (swapGate d) hn rev
    · exact endpts d n hn tail
    · exact endpts (swapGate d) n hn rev

end LocalProof11
end Signed

namespace Small
abbrev W := Nat × Nat

def sep (w : W) := w.1 ^^^ w.2
def op (mask : Nat) (d : Fin 4) (a b : W) : W :=
  match d.val with
  | 0 => (a.1 &&& b.1,a.2 &&& b.2)
  | 1 => (a.1 &&& (mask ^^^ b.1),a.2 &&& (mask ^^^ b.2))
  | 2 => (b.1 &&& (mask ^^^ a.1),b.2 &&& (mask ^^^ a.2))
  | _ => (a.1 ||| b.1,a.2 ||| b.2)

def unionS : List W → Nat
  | [] => 0
  | a :: l => sep a ||| unionS l

def covered (mask : Nat) (ws : List W) := (mask &&& unionS ws) == mask
def kept {α} (save : Bool) (a : α) (xs : List α) := if save then a::xs else xs

theorem cov_perm (mask : Nat) {xs ys : List W} (hp : xs.Perm ys) :
    covered mask xs = covered mask ys := by
  have eq : unionS xs = unionS ys := by
    induction hp with
    | nil => rfl
    | cons a _ ih => simp only [unionS,ih]
    | swap a b rest => simp only [unionS,Nat.or_left_comm]
    | trans _ _ h1 h2 => exact h1.trans h2
  simp only [covered,eq]

inductive Run (mask : Nat) : Nat → List W → Prop
  | stop {w} (hc : covered mask [w] = true) : Run mask 0 [w]
  | perm {k l r} (hp : l.Perm r) (tail : Run mask k l) : Run mask k r
  | step {k a b rest} (d : Fin 4) (ka kb : Bool) (hc : covered mask (a::b::rest) = true)
      (tail : Run mask k (op mask d a b :: kept ka a (kept kb b rest))) :
      Run mask (k+1) (a::b::rest)

theorem Run.cover {mask k l} (h : Run mask k l) : covered mask l = true := by
  induction h with
  | stop c => exact c
  | perm hp _ ih => rwa [← cov_perm _ hp]
  | step _ _ _ c _ _ => exact c

theorem Run.count {mask k l} (h : Run mask k l) : l.length ≤ k+1 := by
  induction h with
  | stop => simp
  | perm hp _ ih => rwa [←hp.length_eq]
  | step d ka kb _ _ ih => cases ka <;> cases kb <;> simp [kept] at ih ⊢ <;> omega

theorem Run.view {mask k l} (h : Run mask k l) :
    (k=0 ∧ l.length=1) ∨
      ∃ j a b r d ka kb, k=j+1 ∧ (a::b::r).Perm l ∧
        Run mask j (op mask d a b :: kept ka a (kept kb b r)) := by
  induction h with
  | stop => exact Or.inl ⟨rfl,rfl⟩
  | perm hp _ ih =>
    rcases ih with ⟨hk,hl⟩ | ⟨j,a,b,r,d,ka,kb,hk,pr,hr⟩
    · exact Or.inl ⟨hk,hp.length_eq.symm.trans hl⟩
    · exact Or.inr ⟨j,a,b,r,d,ka,kb,hk,pr.trans hp,hr⟩
  | @step j a b r d ka kb hc tail _ =>
    exact Or.inr ⟨j,a,b,r,d,ka,kb,rfl,List.Perm.refl _,tail⟩

def guardNext (mask : Nat) (next : List W → Bool) (restSep : Nat) (c : W) (l : List W) :=
  ((mask &&& (sep c ||| restSep)) != mask) || next (c::l)

def tryOp (mask : Nat) (next : List W → Bool) (sl : Nat) (a b : W) (rest : List W)
    (rs : Nat) (d : Fin 4) : Bool :=
  let c := op mask d a b
  guardNext mask next rs c rest &&
    (sl < 1 || (guardNext mask next (sep a ||| rs) c (a::rest) &&
      guardNext mask next (sep b ||| rs) c (b::rest))) &&
    (sl < 2 || guardNext mask next (sep a ||| (sep b ||| rs)) c (a::b::rest))

def tryPair (mask : Nat) (next : List W → Bool) (sl : Nat) (a b : W) (rest : List W) :=
  let alg := tryOp mask next sl a b rest (unionS rest)
  alg 0 && alg 1 && alg 2 && alg 3

def allMoves (mask : Nat) (budget : Nat) (next : List W → Bool) (l : List W) : Bool :=
  let sl := budget+1-l.length
  l.all (fun a =>
    let t := l.erase a
    t.all (fun b => if a.1 ≤ b.1 then tryPair mask next sl a b (t.erase b) else true))

def reject : Nat → Nat → Nat → List W → Bool
  | _,0,_,_ => false
  | mask,fuel+1,budget,l =>
    if l.length < 2 then false
    else if budget = 0 then true
    else allMoves mask budget (reject mask fuel (budget-1)) l

theorem op_swap (mask : Nat) (d : Fin 4) (a b : W) :
    op mask d a b = op mask (FirstOr.swapGate d) b a := by
  fin_cases d <;> simp [op,FirstOr.swapGate,Nat.and_comm,Nat.or_comm]

theorem keep_perm {α} (ka kb : Bool) (a b : α) {r s : List α} (p : r.Perm s) :
    (kept ka a (kept kb b r)).Perm (kept ka a (kept kb b s)) := by
  cases ka <;> cases kb <;> simp only [kept,ite_true,Bool.false_eq_true,ite_false] <;>
    first | exact p | exact p.cons _ | exact (p.cons _).cons _

theorem keep_swap {α} (ka kb : Bool) (a b : α) (r : List α) :
    (kept ka a (kept kb b r)).Perm (kept kb b (kept ka a r)) := by
  cases ka <;> cases kb <;> simp only [kept,ite_true,Bool.false_eq_true,ite_false] <;>
    first | exact List.Perm.refl _ | exact List.Perm.swap _ _ _

theorem pair_checked {mask sl a b r d ka kb j} {next : List W → Bool}
    (p : tryPair mask next sl a b r = true)
    (cap : (if ka then 1 else 0) + (if kb then 1 else 0) ≤ sl)
    (run : Run mask j (op mask d a b :: kept ka a (kept kb b r))) :
    next (op mask d a b :: kept ka a (kept kb b r)) = true := by
  have hd : tryOp mask next sl a b r (unionS r) d = true := by
    simp only [tryPair,Bool.and_eq_true] at p
    fin_cases d
    · exact p.1.1.1
    · exact p.1.1.2
    · exact p.1.2
    · exact p.2
  have cov := run.cover
  cases ka <;> cases kb
  all_goals simp only [kept,ite_true,Bool.false_eq_true,ite_false,covered,unionS,beq_iff_eq] at cov ⊢
  all_goals simp only [tryOp,Bool.and_eq_true,guardNext,Bool.or_eq_true,bne_iff_ne] at hd
  · exact hd.1.1.resolve_left (by simpa using not_not_intro cov)
  · have hsl : ¬ sl < 1 := by simp at cap; omega
    exact ((hd.1.2.resolve_left (by simpa using hsl)).2).resolve_left (by simpa using not_not_intro cov)
  · have hsl : ¬ sl < 1 := by simp at cap; omega
    exact ((hd.1.2.resolve_left (by simpa using hsl)).1).resolve_left (by simpa using not_not_intro cov)
  · have hsl : ¬ sl < 2 := by simp at cap; omega
    exact (hd.2.resolve_left (by simpa using hsl)).resolve_left (by simpa using not_not_intro cov)

theorem moves_sound {mask budget j ws} {next : List W → Bool}
    (ok : allMoves mask budget next ws = true) (cb : j+1 ≤ budget)
    (run : Run mask (j+1) ws) :
    ∃ child, Run mask j child ∧ next child = true := by
  obtain ht | ⟨t,a,b,r,d,ka,kb,eq,p,ht⟩ := run.view
  · omega
  have et : t=j := by omega
  subst t
  have oriented (a b : W) (r : List W) (d : Fin 4) (ka kb : Bool)
      (p : (a::b::r).Perm ws) (order : a.1 ≤ b.1)
      (h : Run mask j (op mask d a b :: kept ka a (kept kb b r))) :
      ∃ child, Run mask j child ∧ next child = true := by
    obtain ⟨am,pa⟩ := List.cons_perm_iff_perm_erase.mp p
    obtain ⟨bm,pb⟩ := List.cons_perm_iff_perm_erase.mp pa
    have f := List.all_eq_true.mp (List.all_eq_true.mp ok a am) b bm
    simp only [order,ite_true] at f
    have pc := (keep_perm ka kb a b pb).cons (op mask d a b)
    have h' := Run.perm pc h
    have lr := p.length_eq
    have lh := h.count
    have cap : (if ka then 1 else 0) + (if kb then 1 else 0) ≤ budget + 1 - ws.length := by
      cases ka <;> cases kb <;> simp [kept] at lr lh ⊢ <;> omega
    exact ⟨_,h',pair_checked f cap h'⟩
  by_cases ho : a.1 ≤ b.1
  · exact oriented a b r d ka kb p ho ht
  · have h' := Run.perm ((keep_swap ka kb a b r).cons _) ht
    rw [op_swap mask d a b] at h'
    exact oriented b a r (FirstOr.swapGate d) kb ka ((List.Perm.swap _ _ _).trans p) (by omega) h'

theorem reject_sound {mask f b ws} (hw : reject mask f b ws = true) :
    ∀ k ≤ b, ¬ Run mask k ws := by
  induction f generalizing b ws with
  | zero => simp [reject] at hw
  | succ f ih =>
    intro k hk run
    simp only [reject] at hw
    split at hw
    · contradiction
    rename_i len
    split at hw
    · rename_i hz
      have h := run.count
      omega
    rename_i nz
    cases k with
    | zero =>
      rcases run.view with h | ⟨j,_,_,_,_,_,_,eq,_,_⟩ <;> omega
    | succ k =>
      obtain ⟨v,hv,ok⟩ := moves_sound hw hk run
      exact ih ok k (by omega) hv
end Small
namespace Small
open FirstOr Signed
noncomputable section LocalProof12

def pack {n : Nat} (f : Fin n → Bool) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn f)).cast (by simp) : BitVec n).toNat

theorem pack_lt {n : Nat} (f : Fin n → Bool) : pack f < 2^n := BitVec.isLt _
theorem pack_bit {n : Nat} (f : Fin n → Bool) (i : Fin n) :
    (pack f).testBit i.val = f i := by
  change ((BitVec.ofBoolListLE (List.ofFn f)).cast (by simp) : BitVec n).getLsbD i.val = _
  rw [BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
  simp [List.getD_eq_getElem?_getD,i.isLt]

theorem pack_high {n : Nat} (f : Fin n → Bool) {j : Nat} (h : n ≤ j) : (pack f).testBit j = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le (pack_lt f) (Nat.pow_le_pow_right (by decide) h))

def project {n} (rows : Bool → Fin n → V → Bool) (f : A) : W :=
  (pack (fun j => f (rows true j)),pack (fun j => f (rows false j)))

theorem project_op {n mask} (hm : mask = 2^n-1) (rows : Bool → Fin n → V → Bool)
    (d : Fin 4) (a b : A) : project rows (gate d a b) = op mask d (project rows a) (project rows b) := by
  have mb (i : Nat) : mask.testBit i = decide (i<n) := by rw [hm,Nat.testBit_two_pow_sub_one]
  apply Prod.ext <;> apply Nat.eq_of_testBit_eq <;> intro j
  all_goals
    by_cases hj : j<n
    · have hi (f : Fin n → Bool) : (pack f).testBit j = f ⟨j,hj⟩ := pack_bit f ⟨j,hj⟩
      fin_cases d <;> simp [project,op,gate,hi,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,mb,hj,Bool.and_comm]
    · have hi (f : Fin n → Bool) : (pack f).testBit j = false := pack_high _ (by omega)
      fin_cases d <;> simp [project,op,hi,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,mb,hj]

theorem project_var {n} (v : V → W) (rows : Bool → Fin n → V → Bool)
    (hr : ∀ s j i, rows s j i = (if s then (v i).1 else (v i).2).testBit j.val)
    (hv : ∀ i, (v i).1 < 2^n ∧ (v i).2 < 2^n) (i : V) :
    project rows (raw i) = v i := by
  apply Prod.ext <;> apply Nat.eq_of_testBit_eq <;> intro j
  all_goals
    by_cases hj : j<n
    · rw [project,pack_bit _ ⟨j,hj⟩]
      first | exact hr true ⟨j,hj⟩ i | exact hr false ⟨j,hj⟩ i
    · rw [project,pack_high _ (by omega)]
      apply Eq.symm
      apply Nat.testBit_lt_two_pow
      apply lt_of_lt_of_le _ (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hj))
      first | exact (hv i).1 | exact (hv i).2

theorem union_bit (ws : List W) (j : Nat) :
    (unionS ws).testBit j = true ↔ ∃ s ∈ ws, (sep s).testBit j = true := by
  induction ws with
  | nil => simp [unionS]
  | cons a ws ih =>
    simp only [unionS,Nat.testBit_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem project_cover {n mask t k S} (hm : mask = 2^n-1) (rows : Bool → Fin n → V → Bool)
    (ht : ∀ s j, t (rows s j) = s) (run : LiveFor t k S) (v : List A) (eqv : v.toFinset = S) :
    covered mask (v.map (project rows)) = true := by
  simp only [covered,beq_iff_eq]
  apply Nat.eq_of_testBit_eq
  intro j
  have mb : mask.testBit j = decide (j<n) := by rw [hm,Nat.testBit_two_pow_sub_one]
  rw [Nat.testBit_and,mb]
  by_cases hj : j<n
  · simp only [hj,decide_true,Bool.true_and]
    let i : Fin n := ⟨j,hj⟩
    have ex : ∃ a ∈ S, a (rows true i) ≠ a (rows false i) := by
      by_contra! all
      have equal := run.agrees all
      rw [ht,ht] at equal
      contradiction
    obtain ⟨a,ha,ne⟩ := ex
    refine (union_bit _ _).2 ⟨project rows a,List.mem_map.mpr ⟨a,List.mem_toFinset.mp (eqv ▸ ha),rfl⟩,?_⟩
    have h1 : (project rows a).1.testBit j = a (rows true i) := pack_bit (fun h => a (rows true h)) i
    have h2 : (project rows a).2.testBit j = a (rows false i) := pack_bit (fun h => a (rows false h)) i
    rw [sep,Nat.testBit_xor,h1,h2]
    cases hp : a (rows true i) <;> cases hn : a (rows false i) <;> simp_all
  · simp [hj]

theorem kept_map {α β} (f : α → β) (d : Bool) (a : α) (r : List α) :
    (kept d a r).map f = kept d (f a) (r.map f) := by cases d <;> rfl
theorem kept_nd {α} (d : Bool) (a : α) (l : List α) (nd : l.Nodup) (na : a ∉ l) :
    (kept d a l).Nodup := by cases d <;> simp [kept,nd,na]
theorem kept_fs (d : Bool) (a : A) (l : List A) :
    (kept d a l).toFinset = if d then insert a l.toFinset else l.toFinset := by
  cases d <;> simp [kept]

theorem project_run {n mask t k S} (hm : mask = 2^n-1) (rows : Bool → Fin n → V → Bool)
    (ht : ∀ s j, t (rows s j) = s) (run : LiveFor t k S) (v : List A)
    (nd : v.Nodup) (eqv : v.toFinset = S) : Run mask k (v.map (project rows)) := by
  induction run generalizing v with
  | stop =>
    have p : [t].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) nd
      simp [eqv]
    have hc := project_cover hm rows ht (LiveFor.stop : LiveFor t 0 {t}) [t] (by simp)
    exact Run.perm (p.map _) (Run.stop hc)
  | @step k U a b d ha hb hab fresh tail ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let after := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have hnd := kept_nd ka a mid bm am
    have eafter : after.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fs,kept_fs,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : gate d a b ∉ after := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (eafter ▸ List.mem_toFinset.mpr hz)))
    have hnew := ih (gate d a b::after) (List.nodup_cons.mpr ⟨hf,hnd⟩) (by simp [eafter])
    change Run _ _ ((gate d a b::kept ka a (kept kb b rest)).map _) at hnew
    rw [List.map_cons,kept_map,kept_map,project_op hm] at hnew
    have p : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) nd
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    have hc := project_cover hm rows ht (LiveFor.step ha hb hab fresh tail) v eqv
    have hc' := (cov_perm mask (p.map (project rows))).trans hc
    exact Run.perm (p.map _) (Run.step d ka kb hc' hnew)

theorem nodup_of_projection {α β} (f : α → β) {xs : List α} (h : (xs.map f).Nodup) : xs.Nodup := by
  induction xs with
  | nil => simp
  | cons a l ih =>
    obtain ⟨na,nd⟩ := List.nodup_cons.mp h
    exact List.nodup_cons.mpr ⟨fun hm => na (List.mem_map_of_mem hm),ih nd⟩

end LocalProof12
end Small
namespace Small
namespace G5
def M : Nat := 0x1ffffff
def w0 : W := (0x21f673,0x212652)
def w1 : W := (0xc6487f,0xc44829)
def w2 : W := (0x1078f9c,0x1038514)
def w3 : W := (0x1f80fe0,0xb00ae0)
def w4 : W := (0x1fff000,0x14ed000)
def w5 : W := (0x0,0x0)
def w6 : W := (0x0,0x0)
def w7 : W := (0x0,0x0)
def w8 : W := (0x0,0x0)
def wires : List W := [w0,w1,w2,w3,w4]
def v : Fin 9 → W := ![w0,w1,w2,w3,w4,w5,w6,w7,w8]
def row (side : Bool) (j : Fin 25) (i : Fin 9) := (if side then (v i).1 else (v i).2).testBit j.val
def g (x : Fin 9 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0)
theorem sample_ok : ∀ s (j : Fin 25), g (row s j) = s := by decide +kernel
end G5
namespace G6
def M : Nat := 0xffffffffffff
def w0 : W := (0x21073f193673,0x210225192652)
def w1 : W := (0x8624c861f87f,0x862488609829)
def w2 : W := (0x3838f181cf9c,0x381071814514)
def w3 : W := (0xc03f01fe0fe0,0xc02f00540ae0)
def w4 : W := (0xffc001fff000,0x358001abf000)
def w5 : W := (0xfffffe000000,0xca7dda000000)
def w6 : W := (0x0,0x0)
def w7 : W := (0x0,0x0)
def w8 : W := (0x0,0x0)
def wires : List W := [w0,w1,w2,w3,w4,w5]
def v : Fin 9 → W := ![w0,w1,w2,w3,w4,w5,w6,w7,w8]
def row (side : Bool) (j : Fin 48) (i : Fin 9) := (if side then (v i).1 else (v i).2).testBit j.val
def g (x : Fin 9 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 0)
theorem sample_ok : ∀ s (j : Fin 48), g (row s j) = s := by decide +kernel
end G6
namespace G7
def M : Nat := 0x7fffffffffffffffffffff
def w0 : W := (0x0,0x0)
def w1 : W := (0x25900918cc0cf1943e7e73,0x25900918c808b194244a52)
def w2 : W := (0x1d30610c93021fc993ff,0x9306104820202891129)
def w3 : W := (0x41e24181f31c3c18f1e39c,0x41424180a31c3c1870e294)
def w4 : W := (0x0,0x0)
def w5 : W := (0x60381fe03e03fe0fe03e0,0x381d402c02b40fe03e0)
def w6 : W := (0x7803fe0003ffc000fffc00,0x5003e40003f74000dbb400)
def w7 : W := (0x7ffc000003ffffff000000,0x7ff40000013dd4bd000000)
def w8 : W := (0x7ffffffffc000000000000,0x2ebc1a2b5c000000000000)
def wires : List W := [w1,w2,w3,w5,w6,w7,w8]
def v : Fin 9 → W := ![w0,w1,w2,w3,w4,w5,w6,w7,w8]
def row (side : Bool) (j : Fin 87) (i : Fin 9) := (if side then (v i).1 else (v i).2).testBit j.val
def g (x : Fin 9 → Bool) : Bool := (x 1 && x 2) || (x 2 && x 3) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
theorem sample_ok : ∀ s (j : Fin 87), g (row s j) = s := by decide +kernel
end G7
end Small
namespace Small
open FirstOr Signed
noncomputable section LocalProof13

namespace G5
def indices : List V := [0,1,2,3,4]
theorem mask_eq : M = 2^25-1 := by decide
theorem pr (i : V) : project row (raw i) = v i :=
  project_var v row (fun _ _ _ => rfl) (by decide +kernel) i
theorem mapped : (indices.map raw).map (project row) = wires := by
  rw [List.map_map]
  simp only [Function.comp_def,pr]
  rfl
theorem list_nodup : (indices.map raw).Nodup :=
  nodup_of_projection (project row) (by rw [mapped]; decide +kernel)
theorem fsraw : (indices.map raw).toFinset = rawBank indices.toFinset := by
  ext a
  simp [rawBank]
def mate : V → V := ![1,2,3,4,0,0,0,0,0]
def single (i j : V) : Bool := decide (j=mate i)
def pair (i j : V) : Bool := single i j || decide (j=i)
theorem deps : ∀ i ∈ indices.toFinset, Depends cycleFive i := by
  have hit : ∀ i ∈ indices.toFinset, cycleFive (single i) ≠ cycleFive (pair i) := by decide +kernel
  intro i hi
  exact ⟨single i,pair i,hit i hi,fun j h => by simp [pair,h]⟩
theorem result (chk : reject M 5 6 wires = true) : FiveAtLeastSeven := by
  intro k Q run sub
  have vi : indices.toFinset = Finset.univ.filter (fun i : V => i.val < 5) := by decide
  have eq : Q = rawBank indices.toFinset := run.raw_start _ (by simpa [cycleBank,vi] using sub) deps
  have ht : ∀ s j, cycleFive (row s j) = s := sample_ok
  have r := project_run mask_eq row ht run (indices.map raw) list_nodup (fsraw.trans eq.symm)
  rw [mapped] at r
  by_contra! small
  exact reject_sound chk k (by omega) r
end G5

namespace G6
def indices : List V := [0,1,2,3,4,5]
theorem mask_eq : M = 2^48-1 := by decide
theorem pr (i : V) : project row (raw i) = v i :=
  project_var v row (fun _ _ _ => rfl) (by decide +kernel) i
theorem mapped : (indices.map raw).map (project row) = wires := by
  rw [List.map_map]
  simp only [Function.comp_def,pr]
  rfl
theorem list_nodup : (indices.map raw).Nodup :=
  nodup_of_projection (project row) (by rw [mapped]; decide +kernel)
theorem fsraw : (indices.map raw).toFinset = rawBank indices.toFinset := by
  ext a
  simp [rawBank]
def mate : V → V := ![1,2,3,4,5,0,0,0,0]
def single (i j : V) : Bool := decide (j=mate i)
def pair (i j : V) : Bool := single i j || decide (j=i)
theorem deps : ∀ i ∈ indices.toFinset, Depends cycleSix i := by
  have hit : ∀ i ∈ indices.toFinset, cycleSix (single i) ≠ cycleSix (pair i) := by decide +kernel
  intro i hi
  exact ⟨single i,pair i,hit i hi,fun j h => by simp [pair,h]⟩
theorem result (chk : reject M 5 7 wires = true) : SixAtLeastEight := by
  intro k Q run sub
  have vi : indices.toFinset = Finset.univ.filter (fun i : V => i.val < 6) := by decide
  have eq : Q = rawBank indices.toFinset := run.raw_start _ (by simpa [cycleBank,vi] using sub) deps
  have ht : ∀ s j, cycleSix (row s j) = s := sample_ok
  have r := project_run mask_eq row ht run (indices.map raw) list_nodup (fsraw.trans eq.symm)
  rw [mapped] at r
  by_contra! small
  exact reject_sound chk k (by omega) r
end G6

namespace G7
def indices : List V := [1,2,3,5,6,7,8]
theorem mask_eq : M = 2^87-1 := by decide
theorem pr (i : V) : project row (raw i) = v i :=
  project_var v row (fun _ _ _ => rfl) (by decide +kernel) i
theorem mapped : (indices.map raw).map (project row) = wires := by
  rw [List.map_map]
  simp only [Function.comp_def,pr]
  rfl
theorem list_nodup : (indices.map raw).Nodup :=
  nodup_of_projection (project row) (by rw [mapped]; decide +kernel)
theorem fsraw : (indices.map raw).toFinset = rawBank indices.toFinset := by
  ext a
  simp [rawBank]
theorem result (chk : ∀ d : Fin 4, reject M 6 8 (op M d w2 w8 :: wires) = true) : EndpointsExcluded := by
  intro d k hk run
  let f := gate d (raw 2) (raw 8)
  let xs := f :: indices.map raw
  have hs : xs.toFinset = insert f thetaRoots := by
    simp only [xs,List.toFinset_cons]
    rw [fsraw]
    have vi : indices.toFinset = thetaV := by decide
    rw [vi,thetaRoots]
  have mappedX : xs.map (project row) = op M d w2 w8 :: wires := by
    change project row (gate d (raw 2) (raw 8)) :: _ = _
    rw [project_op mask_eq,pr,pr,mapped]
    rfl
  have nc : ∀ e : Fin 4, (op M e w2 w8 :: wires).Nodup := by decide +kernel
  have hn : xs.Nodup := nodup_of_projection (project row) (by rw [mappedX]; exact nc d)
  have ht : ∀ s j, thetaGoal (row s j) = s := by
    intro s j; rw [theta_edges]; exact sample_ok s j
  have rr := project_run mask_eq row ht run xs hn hs
  rw [mappedX] at rr
  exact reject_sound (chk d) k hk rr
end G7

end LocalProof13
end Small
namespace Small.G5
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rc5 : reject M 5 6 wires = true := by decide +kernel
end Small.G5
namespace Small.G6
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rc6 : reject M 5 7 wires = true := by decide +kernel
end Small.G6
namespace Small.G7
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rt0 : reject M 6 8 (op M 0 w2 w8 :: wires) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rt1 : reject M 6 8 (op M 1 w2 w8 :: wires) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rt2 : reject M 6 8 (op M 2 w2 w8 :: wires) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rt3 : reject M 6 8 (op M 3 w2 w8 :: wires) = true := by decide +kernel
theorem rt (d : Fin 4) : reject M 6 8 (op M d w2 w8 :: wires) = true := by
  fin_cases d
  · exact rt0
  · exact rt1
  · exact rt2
  · exact rt3
end Small.G7

end CertifiedComponents
end PEqualNP.Outside.L_meta_3823

theorem PEqualNP.Outside.L_meta_3823 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x3 : Fin (9 : ℕ) → Bool) => x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ))) → (13 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4.op.eval [Bool.true]) x1.gates :=
  PEqualNP.Outside.L_meta_3823.Signed.posted_of_theta10 (PEqualNP.Outside.L_meta_3823.Signed.theta_of_cycles
    (PEqualNP.Outside.L_meta_3823.Small.G5.result PEqualNP.Outside.L_meta_3823.Small.G5.rc5)
    (PEqualNP.Outside.L_meta_3823.Small.G6.result PEqualNP.Outside.L_meta_3823.Small.G6.rc6)
    (PEqualNP.Outside.L_meta_3823.Small.G7.result PEqualNP.Outside.L_meta_3823.Small.G7.rt))
