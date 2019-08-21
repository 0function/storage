import group_theory.coset ring_theory.matrix ring_theory.determinant ring_theory.ideals algebra.gcd_domain algebra.euclidean_domain data.int.modeq group_theory.quotient_group data.equiv.algebra group_theory.subgroup tactic.ring tactic.fin_cases tactic.tidy algebra.ring algebra.field linear_algebra.multivariate_polynomial
open tactic native environment sum interactive lean.parser ideal mv_polynomial classical lattice declaration multiset
--local attribute [instance, priority 0] prop_decidable

/-Questions:
	Meta looping or not
	Are orders available
--/

section parameters{J: Type*}[decidable_eq J]{K:Type*}[field K][decidable_eq K]

notation K`:[`:99 J `]` := mv_polynomial J K
notation x`²`:66 := x^2

@[simp] lemma simp_square(x:K): x² = x*x := by{
	change _*_ = _,
	apply congr_arg,
	change _*_ = _,
	apply mul_one,
}

--unique_pairs[xⱼ | j] = [(xᵢ,xⱼ) | i<j]
def list.unique_pairs{T}: list T → list(T×T)
| [] := []
| (x::xs) := xs.map(λy,(x,y)) ++ xs.unique_pairs

def coef(P: K:[J])(m: J→₀ℕ): K := by{
	unfold mv_polynomial at P,
	exact P m,
}

meta def aa := tactic.repeat(interactive.assumption <|> contradiction)


@[reducible] def monomi := J→₀ℕ

private class mo := 
	(ord: decidable_linear_order monomi)
	(neutral_least: ∀ m: monomi, 0 ≤ m)
	(multiplicative: ∀ m n p: monomi, n ≤ m → n+p ≤ m+p)

def monomial_order := mo

instance dlo_mo[mo]: decidable_linear_order monomi := mo.ord
instance[mo]: lattice.semilattice_sup_bot(J→₀ℕ) := {
	bot := 0,
	bot_le := mo.neutral_least,
	sup := λx y, if x ≤ y then y else x,
	sup_le := by{
		intros,
		unfold lattice.has_sup.sup,
		rcases em(a ≤ b); simpa[h],
	},
	le_sup_left := by {
		intros,
		unfold lattice.has_sup.sup,
		rcases em(a ≤ b); simp[h]; aa
	},
	le_sup_right := by{
		intros,
		unfold lattice.has_sup.sup,
		rcases em(a ≤ b); simp[h],
		rcases @linear_order.le_total _ {..mo.ord} a b, aa
	},
..mo.ord}
--True division if n|m, otherwise truncated e.g. xy/x² = y. 
instance[mo]: has_div(J→₀ℕ) := ⟨λm n, finsupp.on_finset m.support (λi, m i - n i) (by{
	intros,
	simp,
	by_contra,
	simp[a_2] at a_1,
	aa,
})⟩


def mv_polynomial.max_mono[mo](P: K:[J]) := P.support.sup id

def mv_polynomial.max_coef[mo](P: K:[J]) := coef P P.max_mono

def scale_monic[mo](P: K:[J]) := C P.max_coef⁻¹ * P

--S-polynomial of a pair of monic polynomials. 
def monicS[mo](PR: K:[J] × K:[J]) := 
	let p:= PR.fst.max_mono, r:= PR.snd.max_mono, M:= p ⊔ r in
	monomial(M/p)1 * PR.fst - monomial(M/r)1 * PR.snd


lemma or_not_if_or{a b : Prop}(h: a ∨ b): a ∨ (¬a ∧ b) := by{
	cases h,
		left, aa,
	cases em a,
		left, aa,
	right, constructor, aa
} 
meta def orn't(h: parse ident): tactic _ := do
	x ← get_local h,
	interactive.have h none ``(or_not_if_or %%x),
	try(clear x),
	get_local h >>=	cases_core,
	swap,
	x ← get_local h,
	n ← get_unused_name h none,
	cases_core x [n,h],
	swap
run_cmd add_interactive [`orn't]


class decidable_founded_order(X: Type*) extends 
	decidable_linear_order X,
	is_well_order X (<),
	has_bot X --This is now always inhabited, but bottom needs to be computable. 
:=(bot_le: ∀a:X, ⊥ ≤ a)

variables{X: Type*}[decidable_founded_order X][decidable_eq X]{S T : multiset X}

instance semilattice_sup_bot_of_linear_order_bot: semilattice_sup_bot X := {
	bot:= ⊥,
	bot_le:= decidable_founded_order.bot_le,
..lattice.lattice_of_decidable_linear_order}

--∑ cⱼ Xʲ ↦ ∑ βʲ | cⱼ≠0
--Kertoimista johtuen polynomien järi ei ole antisymmetrinen. 
--instance{X}: has_coe(finset X)(set X) := ⟨λS, ↑S⟩

--@[reducible] private def top: X → with_top X := some

--def infimum(S: finset X) := match S.inf top with some n := n | _ := ⊥ end

private def IM(S: finset X) := S≠∅ → S.sup id ∈ S
lemma maximum_mem{S: finset X}: IM S := by{
	have emp: IM(∅: finset X), aa,
	have: ∀x, ∀ S: finset X, x ∉ S → IM S → IM(insert x S),
		unfold IM,
		intros,
		cases em(S_1 = ∅); simp[h] at *,
		simp[has_sup.sup,semilattice_sup.sup,semilattice_sup_bot.sup,lattice.sup,max],
		cases em(x ≤ S_1.sup id); simp[h_1],
		right,aa,
	apply finset.induction emp this,
}

@[simp] lemma not_or_eq_not_and_not{a b : Prop}: (¬(a ∨ b)) = (¬a ∧ ¬b) := by{
	ext,
	constructor;intro,
	repeat{cases em a; simp [h] at *, aa},
}

lemma gt_neq{X: Type u_3}[linear_order X]{x y : X}(h: x>y): ¬ x=y := by{
	by_contra,
	rw a at h,
	exact lt_irrefl _ h,
}

@[simp] lemma gt_sup{x y z : X}: (x > y ⊔ z) = (x>y ∧ x>z) := by{
	ext,
	constructor; intro h,
		constructor,
			apply gt_of_gt_of_ge h (le_sup_left),
		apply gt_of_gt_of_ge h (le_sup_right),
	cases h with xy xz,
	simp[has_sup.sup,semilattice_sup.sup,semilattice_sup_bot.sup,lattice.sup,max],
	cases em(y≤z); simp[h], aa
}

private def ILNM(S: finset X) := ∀x, S≠∅ → x > S.sup id → x ∉ S
lemma maximum_more_not_mem{S: finset X}: ILNM S := by{
	have emp: ILNM(∅: finset X), intro, aa,
	have: ∀x, ∀ S: finset X, x ∉ S → ILNM S → ILNM(insert x S),
		unfold ILNM,
		intros,
		cases em(S_1 = ∅); simp[h] at *,
			apply gt_neq, aa,
		cases a_3,
		constructor,
			apply gt_neq _, aa,
		apply a_1, aa,
	apply finset.induction emp this,
}

lemma maximum_is_largest{S: finset X}{x:X}(h: x ∈ S): S.sup id ≥ x := by{
	cases lt_or_ge (S.sup id) x, swap, aa,
	cases em(S=∅), simp[h_2] at h, aa,
	have:= maximum_more_not_mem _ h_2 h_1, aa,
}

def dif_set(S T : multiset X) := (S∪T).to_finset.filter(λx, S.count x ≠ T.count x)

lemma neq_comm(x y : X): (x≠y) = (y≠x) := by tidy

lemma dif_set_com: dif_set S T = dif_set T S := by{
	unfold dif_set,
	rw multiset.union_comm,
	apply congr_fun,
	have: (λx, S.count x ≠ T.count x) = (λx, T.count x ≠ S.count x),
		ext,
		simp,
		constructor; tidy,
	simp only[this],
	apply congr_arg,
	tidy,
}

lemma multiset_ext(h: ∀x, x ∈ (S∪T).to_finset → S.count x = T.count x): S = T := by{
	ext,
	cases em(a ∈ (S∪T).to_finset),
		apply h a h_1,
	tidy,
	rw[list.count_eq_zero_of_not_mem h_1_left,list.count_eq_zero_of_not_mem h_1_right],
}

lemma dif_set_nonempty(h: S≠T): dif_set S T ≠ ∅ := by{
	by_contra,
	simp at a,
	have SeT: ∀ x, x ∈ (S∪T).to_finset → S.count x = T.count x,
		intros,
		by_contra,
		have: x ∈ dif_set S T := finset.mem_filter.mpr⟨a_1,a_2⟩,
		simp[a] at this, aa,
	apply h,
	apply multiset_ext SeT,
}

lemma more_maximum_dif_set{x:X}(h: x > (dif_set S T).sup id): S.count x = T.count x := by{
	cases em(S=T), rw[h_1],
	have:= maximum_more_not_mem _ (dif_set_nonempty h_1) h,
	simp[dif_set] at this,
	cases em(x∈S ∨ x∈T),
		exact this h_2,
	tidy,
	rw[multiset.count_eq_zero_of_not_mem h_2_left,multiset.count_eq_zero_of_not_mem h_2_right],
}

lemma mem_dif_set{x:X}(h: S.count x ≠ T.count x): x ∈ dif_set S T := by{
	simp[dif_set],
	constructor, swap, aa,
	by_contra,
	simp at a,
	cases a,
	rw[multiset.count_eq_zero_of_not_mem a_left,multiset.count_eq_zero_of_not_mem a_right] at h,
	aa,
}

lemma max_dif_is_maximum_dif_set{x:X}(h: S.count x ≠ T.count x ∧ ∀y, y>x → S.count y = T.count y): x = (dif_set S T).sup id := by{
	cases h with d a,
	have:= lt_or_eq_of_le(maximum_is_largest(mem_dif_set d)),
	cases this, swap, exact this,
	cases em(S=T), simp[h] at d, aa,
	have ei:= a _ this,
	have di:= maximum_mem(dif_set_nonempty h),
	simp[dif_set] at di,
	cases di, aa,
}

meta def unlet(n: parse ident)(h: parse ident): tactic _ := do
	expr.elet _ t b e ← get_local_type h,
	tactic.definev n t b,
	n' ← get_unused_name n none,
	v ← get_local n,
	interactive.have n' ``(%%v = %%b) ``(rfl),
	v ← get_local n',
	interactive.simp none tt [simp_arg_type.expr``(eq.symm %%v)] [] (loc.ns[some h])
run_cmd add_interactive [`unlet]

lemma or_simp_{A: Type u_3}{p r}{a b : A}(h: p ∨ a=b ∨ r): (a=b ∨ p) ∨ (b=a ∨ r) := by{
	rcases h with h|h|h,
			left,right,aa,
		left,left,aa,
	right,right,aa,
}

lemma eq_at_maximum_dif_set: (S.count((dif_set S T).sup id) = T.count((dif_set S T).sup id)) = (S=T) := by{
	ext,
	constructor;
		intro h,
		by_contra,
		have:= maximum_mem(dif_set_nonempty a),
		simp[dif_set] at this,
		exact this.right h,
	rw h,
}

lemma neq.symm{X:Type}{x y : X}(h: x≠y): y≠x := by finish

instance: linear_order(multiset X) := {
	le := λS T, S=T ∨ let x := (dif_set S T).sup id in S.count x < T.count x,
	le_refl := by simp,
	le_antisymm := by{
		intros,
		cases a_1, aa,
		cases a_2, exact a_2.symm,
		rw dif_set_com at a_2,
		have:= lt_irrefl _ (lt.trans a_1 a_2), aa,
	},
	le_trans := by{
		intros a b c ab bc,
		orn't ab, rw ab, aa,
		orn't bc, rw ←bc, right, aa,
		unlet x ab,
		unlet y bc,
		right,
		rcases lt_trichotomy x y with h|h|h, swap 3,
				rw y_1 at h,
				have ee:= (more_maximum_dif_set h).symm,
				have: x = (dif_set a c).sup id,
					apply max_dif_is_maximum_dif_set,
					constructor,
						rw ee,
						apply neq.symm,
						apply gt_neq , aa,
					intros z v,
					rw ← more_maximum_dif_set(gt.trans v h),
					rw x_1 at v,
					exact more_maximum_dif_set v,
				rw this.symm at *,
				simpa[ee],
			swap,
			rw ←h at bc,
			have: x = (dif_set a c).sup id,
				apply max_dif_is_maximum_dif_set,
				constructor,
					apply neq.symm,
					apply gt_neq,
					exact lt.trans ab bc,
				intros z v,
				rw [h,y_1] at v,
				rw ← more_maximum_dif_set v,
				rw [←y_1,←h,x_1] at v,
				exact more_maximum_dif_set v,
			simp[this.symm],
			exact lt.trans ab bc,
		rw x_1 at h,
		have ee:= (more_maximum_dif_set h),
		have: y = (dif_set a c).sup id,
			apply max_dif_is_maximum_dif_set,
			constructor,
				rw ee,
				apply neq.symm,
				apply gt_neq _, aa,
			intros z v,
			rw more_maximum_dif_set(gt.trans v h),
			rw y_1 at v,
			exact more_maximum_dif_set v,
		rw this.symm at *,
		simpa[ee],
	},
	le_total := by{
		intros,
		simp,
		rw @dif_set_com _ _ _ b a,
		apply or_simp_,
		rw ←(eq_at_maximum_dif_set: _ = (a=b)),
		apply lt_trichotomy,
	},
}

private def less := @has_lt.lt 
	(multiset X) (@preorder.to_has_lt 
	(multiset X) (@partial_order.to_preorder 
	(multiset X) (@linear_order.to_partial_order 
	(multiset X) multiset.linear_order)))

instance: has_lt(multiset X) := ⟨less⟩
instance it_: is_trichotomous (multiset X) (<) := ⟨lt_trichotomy⟩

local infix `•`:66 := multiset.repeat

private def SM(S: multiset X) := S.sup ∈ S ∨ S=∅
lemma sup_mem: SM S := by{
	apply multiset.case_strong_induction_on; unfold SM, tidy,
	left,
	rw(_: multiset.sup↑(list.cons a s) = a ⊔ multiset.sup s),
	simp[has_sup.sup,semilattice_sup.sup,semilattice_sup_bot.sup,lattice.sup,max] at *,
	cases em(a ≤ multiset.sup s); simp[h],
	cases em(s=[]), simp[h_1,multiset.sup] at *, apply eq.symm,aa,
	right,
	cases a_1 s (by refl),aa,
	rw((multiset.coe_eq_zero s).mp h_2) at h_1,aa,refl,
}

lemma sup_mem'(h: S≠∅): S.sup ∈ S := by{cases sup_mem, aa}

lemma nonbottom_sup_mem(h: sup S ≠ ⊥): sup S ∈ S := by{
	cases em(S=∅),
		simp[h_1] at h, aa,
	apply sup_mem' h_1,
}

lemma not_lt_0: ¬ S<0 := by{
	simp[has_lt.lt,less,preorder.lt,partial_order.lt,linear_order.lt,preorder.lt._default,partial_order.lt._default],
	intros,
	cases a, simp[a] at *,aa,
	cases a,
}

lemma multiset_lt_def(ts: T<S): T.count((dif_set T S).sup id) < S.count((dif_set T S).sup id) := by{
	simp[has_lt.lt,less,preorder.lt,partial_order.lt,linear_order.lt,partial_order.lt._default,preorder.lt._default] at ts,
	rw(_: dif_set S T = dif_set T S) at ts,
	rw(_: (S=T) = (T=S)) at ts,
	cases em(T=S); simp[h] at *, aa,
	exact ts.left,
ext, constructor; apply eq.symm,
apply dif_set_com,
}

lemma sup_le_sup_of_lt(ts: T < S): T.sup ≤ S.sup := by{
	let x:= (dif_set S T).sup id,
	cases em(T=∅), simp[h],
	by_contra,
	have Tne0: T.count T.sup ≠ 0,
		by_contra,
		simp at a_1,
		apply count_eq_zero.mp a_1,
		cases sup_mem, aa,
	have Seq0: S.count T.sup = 0,
		apply count_eq_zero.mpr,
		by_contra,
		have:= le_sup a_1, aa,
	rw ←Seq0 at Tne0,
	have jlk:= maximum_is_largest (mem_dif_set Tne0),
	have S0: S.count((dif_set T S).sup id) = 0,
		apply count_eq_zero.mpr,
		by_contra,
		have:= le_trans jlk (le_sup a_1), aa,
	have:= multiset_lt_def ts,
	simp[S0] at this,
	cases this,
}

def under(x)(S: multiset X) := S.sup < x

lemma under_of_lt_under{x}(ts: T < S)(u: under x S): under x T := by{
	have:= sup_le_sup_of_lt ts,
	apply lt_of_le_of_lt, aa,
}

@[simp] lemma sup_repeat_bot{n}: (⊥•n).sup = (⊥:X) := by{
	induction n; simp,
		refl,
	rw n_ih,
	simp,
}

lemma sup_repeat_le{n}{x:X}: sup(x•n) ≤ x := by{
	induction n; simp,
	constructor,
		refl,
	aa
}

lemma repeat_le_of_le{n m}{x:X}(h: n≤m): 
	@has_le.le 
	(multiset X) (@preorder.to_has_le 
	(multiset X) (@partial_order.to_preorder 
	(multiset X) (@linear_order.to_partial_order 
	(multiset X) multiset.linear_order)))
	(x•n) (x•m) := by{
	let d:= (dif_set (x•n) (x•m)).sup id,
	have df: d = (dif_set (x•n) (x•m)).sup id := rfl,
	change _ ∨ _ < _,
	rw ←df,
	cases eq_or_lt_of_le h,
		left,
		rw h_1,
	right,
	have: dif_set (x•n) (x•m) = {x},
		ext,
		constructor; intro; simp * at *,
			unfold dif_set at a_1,
			have: a ∈ to_finset(x•n ∪ x•m) := finset.filter_subset _ a_1,
			simp at this,
			cases this; exact eq_of_mem_repeat(by aa),
		apply mem_dif_set,
		simp,
		by_contra,
		rw ←a_2 at *,
		exact lt_irrefl _ h_1,
	simp[this, finset.sup, df] at *, aa,
}

lemma lt_of_repeat_lt{n m}{x:X}(h: x•n < x•m): n<m := by{
	by_contra,
	simp at a,
	have:= not_lt_of_ge (repeat_le_of_le a), aa
}

@[simp] lemma count_repeat_other{x y : X}{n}(h: x≠y): count x (y•n) = 0 := by{
	induction n; simp[count_cons_of_ne h], aa
}

@[simp] lemma not_lt_bot{x:X}: ¬ x < ⊥ := by{simp, apply bot_le}

@[simp] lemma mem_dif_set_eq_count_ne_count{x:X}: (x ∈ dif_set S T) = (count x S ≠ count x T) := by{
	ext, constructor; intro,
		apply (finset.mem_filter.mp a).right,
	apply mem_dif_set a,
}

@[simp] lemma dif_set_same: dif_set S S = ∅ := by{ext, constructor; simp}

@[simp] lemma count_repeat{x y : X}{n}: count x (y•n) = ite(x=y) n 0 := by{cases em(x=y); simp[h]}

lemma not_lt_self_sub{n m : ℕ}: ¬ n < n-m := by{
	by_contra,
	apply lt_irrefl _ (calc n+m < n : nat.add_lt_of_lt_sub_right a
		... = n+0 : by simp
		... ≤ n+m : nat.add_le_add_left(_:0≤m) n),
	tidy,
}

lemma stupid{n m : ℕ}(h: nat.lt n m): n<m := by finish

lemma eq_repeat_bot_of_sup_bot(h: sup S = ⊥): S = ⊥ • count ⊥ S := by{
	tidy,
	cases em(a=⊥); simp[h_1],
	induction S; simp[sup] at *,
	cases sup_eq_bot_iff.mp h with h_ t_,
	rw list.count_cons_of_ne, apply S_ih t_,
	rw h_, aa
}

private def IX := λx, ∀P: multiset X → Prop, (∀S, under x S → (∀T, T<S → P T) → P S) → ∀S, under x S → P S

private lemma AIX: ∀(x:X), IX x := by{
	intro,
	apply @well_founded.induction _ (<) _inst_4.wf IX,
	intros x ihX,
	intros P ihP S Sx,
	cases em(S=∅) with SO,
		simp[SO] at *,
		apply ihP 0,aa,
		intros,
		have:= not_lt_0 a,aa,
	let y := sup S,
	let with_y := λn(s: multiset X), s - y• count y s + y•n,
	have count_with_y: ∀z m J, count z (with_y m J) = if z=y then m else count z J,
		intros,
		cases em(z=y); simp[h_1, with_y],
	have with_y_split: ∀Z, Z = with_y (count y Z) (with_y 0 Z), 
		intro, ext, simp[count_with_y],
		cases em(a=y); simp[h_1],
	let N := λn, ∀T, under y T → P(with_y n T),
	have AN: ∀n, N n,
		intro,
		apply @nat.strong_induction_on N,
		intros n ihN T Ty,
		apply ihX y Sx (P ∘ with_y n) _ T (by aa),
		simp,
		intros T Ty ihXy,
		apply ihP,
			apply lt_of_le_of_lt _ Sx,
			simp[with_y,under],
			constructor,
				calc sup (T - y•count y T) ≤ sup T : sup_mono(subset_of_le(multiset.sub_le_self _ _))
				... ≤ sup S : le_of_lt Ty,
			apply sup_repeat_le,
		intros J JT,
		let J₀ := with_y 0 J,
		have Jis: J = with_y (count y J) J₀ := with_y_split J,
		rw Jis,
		have J₀y: under y J₀, 
			cases em(y=⊥),
				simp[h_1,under] at Ty, aa,
			have: sup J₀ ≤ y,
				change sup(with_y _ _) ≤ _,
				simp[with_y],
				apply le_trans(sup_mono(subset_of_le(multiset.sub_le_self _ _)) : sup(J - y• count y J) ≤ sup J),
				apply le_trans ∘ sup_le_sup_of_lt, aa,
				simp[with_y],
				constructor, apply sup_repeat_le,
				apply le_of_lt(lt_of_le_of_lt(sup_mono(subset_of_le(multiset.sub_le_self _ _)))Ty),
			cases lt_or_eq_of_le this, aa,
			rw ←h_2 at h_1,
			have:= nonbottom_sup_mem h_1,
			rw h_2 at this,
			have:= count_eq_zero.mp _, aa, simp,
		have Jy_n: count y J ≤ n,
			by_contra,
			simp at a,
			rw(by simp : n = count y (with_y n T)) at a,
			have JT := multiset_lt_def JT,
			have: y = (dif_set J (with_y n T)).sup id,
				apply max_dif_is_maximum_dif_set,
				constructor, apply ne_of_gt a,
				intros z yz,
				have Tz0: ∀ z>y, count z (with_y n T) = 0,
					intros z yz,
					simp[count_with_y, ne_of_gt yz],
					apply count_eq_zero_of_not_mem,
					by_contra,
					apply lt_irrefl _(calc z ≤ sup T : le_sup a_1
						... < y : Ty
						... < z : yz),
				cases em(count z J > 0), swap, rw Tz0, simp at h_1, aa,
				by_contra,
				have: id z ≤ _ := finset.le_sup(mem_dif_set a_1),
				simp at this,
				rw(Tz0 _ (lt_of_lt_of_le yz this)) at JT,
				cases JT,
			rw ←this at JT,
			apply lt_irrefl _ (lt.trans a JT),
		cases eq_or_lt_of_le Jy_n,
			rw h_1, rw[Jis,h_1] at JT,
			have: J₀ < T,
				have difs: dif_set J₀ T = dif_set (with_y n J₀) (with_y n T),
					have: count y T = 0,
						apply count_eq_zero_of_not_mem,
						by_contra,
						apply lt_irrefl _ (calc y ≤ sup T : le_sup a ... < y : Ty),
					ext, constructor; intro m; simp at *; rw this at *; simp at *, aa,
				have JT:= multiset_lt_def JT,
				rw ←difs at JT,
				have ei'y: ¬ (dif_set J₀ T).sup id = y,
					by_contra on'y,
					cases em(dif_set J₀ T = ∅) with emp, simp[emp,on'y.symm] at *, apply lt_irrefl _ JT,
					have:= maximum_mem h_2,
					rw[on'y,difs] at this,
					simp at this, aa,
				simp[has_lt.lt,less,preorder.lt,partial_order.lt,linear_order.lt,partial_order.lt._default,preorder.lt._default],
				rw(dif_set_com : dif_set T J₀ = _),
				simp[count_with_y,ei'y] at *,
				constructor, right, aa,
				constructor; by_contra f, simp[f] at *, apply not_lt_self_sub JT,
				apply lt_irrefl _ (lt_trans (stupid f) JT),
			apply ihXy J₀ this,
		apply ihN _ h_1 _ J₀y,
	cases em(y=⊥),
		let P_ := λn, P(⊥•n),
		have AP_: ∀n, P_ n,
			intro,
			simp[P_],
			apply @nat.strong_induction_on P_,
			intros n ih,
			apply ihP, simp[under], rw ←h_1, aa,
			intros,
			have:= eq_repeat_bot_of_sup_bot(le_bot_iff.mp(calc sup T ≤ sup(⊥•n) : sup_le_sup_of_lt(by aa) ... = ⊥ : by simp)),
			rw this at *,
			apply ih _ (lt_of_repeat_lt a),
		rw(eq_repeat_bot_of_sup_bot h_1),
		apply AP_,
	rw(with_y_split S),
	apply AN (count y S) (with_y 0 S),
	simp[with_y, under],
	cases lt_or_eq_of_le(sup_mono(subset_of_le(multiset.sub_le_self _ _))), aa, 
	cases (sup_mem: SM(S - y• count y S)), 
		rw h_2 at h_3,
		have: count y (with_y 0 S) = 0, simp,
		have:= count_eq_zero.mp this,
		simp[with_y] at this, aa,
	simp[h_3],
	cases lt_or_eq_of_le(bot_le: ⊥≤y), aa, rw ←h_4 at h_1, aa,
}

instance iwo_: is_well_order (multiset X) (<) := ⟨by{
	have induction: ∀P: multiset X → Prop, (∀S, (∀T, T<S → P T) → P S) → ∀S, P S,
		have AIX: ∀x, IX x := @AIX X _ _,			
		intros,
		let y := sup S,
		let with_y := λn(s: multiset X), s - y• count y s + y•n,
		have count_with_y: ∀z m J, count z (with_y m J) = if z=y then m else count z J,
			intros,
			cases em(z=y); simp[h, with_y],
		have with_y_split: ∀Z, Z = with_y (count y Z) (with_y 0 Z), 
			intro, ext, simp[count_with_y],
			cases em(a_1=y); simp[h],
		cases em(y=⊥) with y_ y'_,
			rw(eq_repeat_bot_of_sup_bot y_),
			generalize: count ⊥ S = n,
			apply @nat.strong_induction_on(λn, P(⊥•n)),
			simp,
			intros n ih,
			apply a,
			intros,
			have:= eq_repeat_bot_of_sup_bot(le_bot_iff.mp(calc sup T ≤ sup(⊥•n) : sup_le_sup_of_lt(by aa) ... = ⊥ : by simp)),
			rw this at *,
			apply ih _ (lt_of_repeat_lt a_1),
		let R := λn, ∀T, under y T → P(with_y n T),
		have AR: ∀n, R n,
			intro,
			apply @nat.strong_induction_on R, intros n ihR T,
			apply AIX y, intros T Ty ih,
			apply a, intros t t_Tn,
			have ty_n: count y t ≤ n,
				by_contra a,
				simp at a,
				rw(by simp : n = count y (with_y n T)) at a,
				have JT := multiset_lt_def t_Tn,
				have: y = (dif_set t (with_y n T)).sup id,
					apply max_dif_is_maximum_dif_set,
					constructor, apply ne_of_gt a,
					intros z yz,
					have Tz0: ∀ z>y, count z (with_y n T) = 0,
						intros z yz,
						simp[count_with_y, ne_of_gt yz],
						apply count_eq_zero_of_not_mem,
						by_contra,
						apply lt_irrefl _(calc z ≤ sup T : le_sup a_1
							... < y : Ty
							... < z : yz),
					cases em(count z t > 0), swap, rw Tz0, simp at h, aa,
					by_contra,
					have: id z ≤ _ := finset.le_sup(mem_dif_set a_1),
					simp at this,
					rw(Tz0 _ (lt_of_lt_of_le yz this)) at JT,
					cases JT,
				rw ←this at JT,
				apply lt_irrefl _ (lt.trans a JT),
			let t₀ := with_y 0 t,
			rw(with_y_split t),
			cases lt_or_eq_of_le ty_n with c c,
				apply ihR(count y t), aa,
				simp[with_y, under],
				cases lt_or_eq_of_le(calc sup t ≤ sup(with_y n T) : sup_le_sup_of_lt t_Tn
					... = sup _ ⊔ sup(y•n) : by simp
					... ≤ sup T ⊔ y : sup_le_sup (sup_mono(subset_of_le(multiset.sub_le_self _ _))) sup_repeat_le
					... ≤ y ⊔ y : sup_le_sup (le_of_lt Ty) (by refl)
					... = y : by simp)
				with t_lt_y t_eq_y,
					calc sup(t - y• count y t) ≤ sup t : sup_mono(subset_of_le(multiset.sub_le_self t (y• count y t)))
					... < y : t_lt_y,
				cases lt_or_eq_of_le(sup_mono(subset_of_le(multiset.sub_le_self t (y• count y t)))),
					calc sup(t - y• count y t) < sup t : h
					... ≤ sup(with_y n T) : sup_le_sup_of_lt t_Tn
					... = sup _ ⊔ sup(y•n) : by simp
					... ≤ sup T ⊔ y : sup_le_sup (sup_mono(subset_of_le(multiset.sub_le_self _ _))) sup_repeat_le
					... ≤ y ⊔ y : sup_le_sup (le_of_lt Ty) (by refl)
					... = y : by simp,
				cases (sup_mem: SM(t - y• count y t)),
					rw h at h_1,
					have: count y (with_y 0 t) = 0, simp,
					have:= count_eq_zero.mp this,
					simp[with_y,t_eq_y] at *, aa,
				simp[h_1],
				cases lt_or_eq_of_le(bot_le: ⊥≤y), aa, rw ←h_2 at y'_, aa,
			rw c,
			apply ih,
			have difs: dif_set t₀ T = dif_set (with_y n t₀) (with_y n T),
				have: count y T = 0,
					apply count_eq_zero_of_not_mem,
					by_contra a,
					apply lt_irrefl _ (calc y ≤ sup T : le_sup a ... < y : Ty),
				ext, constructor; intro m; simp at *; rw this at *; simp at *, aa,
			have JT:= multiset_lt_def t_Tn,
			have et: with_y _ t₀ = t := (with_y_split t).symm,
			rw c at et,
			rw et at difs,
			rw ←difs at JT,
			have ei'y: ¬ (dif_set t₀ T).sup id = y,
				by_contra on'y,
				cases em(dif_set t₀ T = ∅) with emp, simp[emp,on'y.symm] at *, rw c at JT, apply lt_irrefl _ JT,
				have:= maximum_mem h,
				rw[on'y,difs] at this,
				simp at this, aa,
			simp[has_lt.lt,less,preorder.lt,partial_order.lt,linear_order.lt,partial_order.lt._default,preorder.lt._default],
			rw(dif_set_com : dif_set T t₀ = _),
			simp[count_with_y,ei'y] at *,
			constructor, right, aa,
			constructor; by_contra f, simp[f] at *, apply not_lt_self_sub JT,
			apply lt_irrefl _ (lt_trans (stupid f) JT),
		rw(with_y_split S),
		apply AR,
		simp[with_y, under],
		cases lt_or_eq_of_le(sup_mono(subset_of_le(multiset.sub_le_self _ _))), aa, 
		cases (sup_mem: SM(S - y• count y S)),
			rw h at h_1,
			have: count y (with_y 0 S) = 0, simp,
			have:= count_eq_zero.mp this,
			simp[with_y] at this, aa,
		simp[h_1],
		cases lt_or_eq_of_le(bot_le: ⊥≤y), aa, rw ←h_2 at y'_, aa,
	apply well_founded.intro,
	apply induction,
	intros,
	constructor,aa
}⟩

open finsupp

instance mo_ord_J[mo]: decidable_linear_order J := {
	le := λi j, single i 1 ≤ single j 1,
	le_trans := by finish,
	le_refl := by finish,
	le_antisymm := by{
		intros a b a_1 a_2, dsimp at *,
		have:= congr_arg (λm, (support m).1) (le_antisymm a_1 a_2),
		simp[support_single_ne_zero] at this, aa
	},
	le_total := by{
		intros, simp at *,
		cases le_total (single a 1) (single b 1), left, aa, right, aa
	},
	decidable_le := by apply_instance,
}
#check 1

instance endomonoid{t}: monoid(t → t) := {
	one := id,
	mul := (∘),
	mul_assoc := function.comp.assoc,
	one_mul := function.comp.left_id,
	mul_one := function.comp.right_id,
}

theorem founded_iff_no_strictly_decreasing_seq{X}[partial_order X]: @well_founded X (<) ↔ ¬∃s: ℕ→X, ∀i j, i<j → s i > s j := by{
	constructor; intro,
		-- by_contra,
		-- cases a_1 with s d,
		-- let sℕ := s '' set.univ,
		-- have: sℕ ≠ ∅, safe,
		-- let x := a.min sℕ ‹sℕ ≠ ∅›,
		-- rcases a.min_mem sℕ ‹sℕ ≠ ∅› with ⟨j, _, sj_x⟩,
		-- have:= d j (j+1) (by constructor),
		-- have:= a.not_lt_min sℕ ‹sℕ ≠ ∅› (by tidy : s(j+1) ∈ sℕ),
		-- rw sj_x at *, aa,
		sorry,
	
}

structure strictly_increasing_maps(X Y)[partial_order X][partial_order Y] := (f: X→Y) (si: ∀x y, x<y → f x < f y)
infixr ` ⤤ `:20 := strictly_increasing_maps

--def 𝓒{X Y}(x:X)(y:Y) := x

--instance{X Y}[partial_order X][partial_order Y]: has_coe_to_fun(X⤤Y) := ⟨λ_,X→Y, strictly_increasing_maps.f⟩

def is_subsequence{A:Type}(s t : ℕ→A) := ∃j: ℕ→ℕ, (∀n m, n<m → j n < j m) ∧ s = t∘j
infix ` ⊴ `:50 := is_subsequence
variable{A:Type}

@[refl] theorem subseq_refl(s: ℕ→A): s⊴s := ⟨id, by safe⟩
@[trans] theorem subseq_trans(a b c : ℕ→A)(ab: a⊴b)(bc: b⊴c): a⊴c := by{
	rcases ab with ⟨j,_⟩,
	rcases bc with ⟨k,_⟩,
	exact⟨k∘j, by safe⟩
}

def build(next: list A → A): ℕ→A := λn, next(((λe, e++[next e]) ^n) [])


--An order is extensibly founded if each of its extensions is well founded. Presence of an increasing pair in every sequence is a technically easier formulation. 
class extensibly_founded(X) extends partial_order X := (ef: ∀s: ℕ→X, ∃ i j, i<j ∧ s i ≤ s j)

/-Jos jokaiselle i olisi <∞ monta j>i s.e. si≤sj, niin voitaisiin rekursiivisesti valita jono, jossa mikään alkio ei ole suurempi kuin jokin edeltäjänsä, rr. Täten voidaan valita rekursiivisesti osajonoon vain sellaisia termejä, joita seuraa ∞ monta suurempaa termiä. 
Ol. ∃s, ∀i, #{j>i | si≤sj} < ∞.
	build(js ↦ ε\U{i>⊔js | ∃ j∈js: si≤sj} --∃, koska #U{...} < ∞)  contradicts ef
Siis ∀s, ∃i, #{j>i | si≤sj} = ∞. Olk. gi ⊴ s|>i s.e. gij>si, jossa i saadaan valinnalla edellisestä. Muodostetaan jono (gⁱs)0 ja osoitetaan se kasvavaksi. 
--/
theorem E_inc_subseq{X}[extensibly_founded X]: ∀s: ℕ→X, ∃ t⊴s, monotone t := sorry

local attribute [instance, priority std.priority.default+1] prod.partial_order

instance{X Y}[extensibly_founded X][extensibly_founded Y]: extensibly_founded(X×Y) := ⟨by{
	sorry
}⟩

instance: has_dvd(J→₀ℕ) := ⟨λn m, ∀ j ∈ n.support, n j ≤ m j⟩
instance lo_mo[mo]: linear_order monomi := {..dlo_mo}

instance iwo_mo[mo]: is_well_order monomi (<) := ⟨by{
	--Järjestys laajentaa laajapohjustettua tulojärjestystä olettaen, että #J<∞. 
	sorry
}⟩

--set_option trace.class_instances true
instance dfo_monomi[mo]: decidable_founded_order monomi := {
	bot := 0,
	bot_le := by safe,
	..dlo_mo,
	..iwo_mo
}

def polyprec[mo](P R : K:[J]) := P.support.1 < R.support.1
local notation ` ≺ `:50 := polyprec

instance[mo]: has_well_founded(K:[J]) := ⟨(≺), by{
	have: polyprec = inv_image (<) (λ(P: K:[J]), P.support.1) := rfl,
	rw this,
	apply inv_image.wf,
	apply iwo_.wf,
}⟩

--Simplify the top term. Note: This may not simplify P at all if it is not the case that P→0. 
def simplify_step[mo](B: list(K:[J]))(P: K:[J]) := 
	let p := P.max_mono, b := B.map mv_polynomial.max_coef in
	match B.filter(λb:K:[J], b.max_mono ∣ p) with
	| [] := P
	| (b::_) := P - C(P.max_coef / b.max_coef) * b
end

--How to best implement: meta or with proof?
def simplify[mo](B: list(K:[J]))(P: K:[J]): K:[J] := sorry

--1. simplify is a non-trivially terminating loop
--2. the S-polynomial generation surrounds a call to simplify
--3. the main loop is non-trivially terminating
--⟹ correctness of S-step can't be proven without simplify, ...right?

private meta def go[mo]: list(K:[J]) → list(K:[J] × K:[J]) → list(K:[J])
| G [] := G
| G (p::ps) := let s := scale_monic(simplify G (monicS p)) in
	if s=0 then go G ps else
		go (s::G) (ps ++ G.map(λP, (P,s)))


meta def Gr'LeanHasLetterBug'bner_basis_of[mo](B: list(K:[J])) := let B1 := B.map scale_monic in go B1 B1.unique_pairs end
notation `Gröbner_basis_of` := Gr'LeanHasLetterBug'bner_basis_of

#exit
def spans{R}[comm_ring R](s: list R) := span(set_of(flip list.mem s))

example: (X 1 ² - X 2 ² : mv_polynomial ℕ K) ∈ spans[X 1 ² * X 2 - X 1 ², (X 2 ² * X 1 - X 2 ² : K:[J])] := by{
	let A: K:[J] := X 1 ² * X 2 - X 1 ²,
	let B: K:[J] := X 2 ² * X 1 - X 2 ²,
	let C: K:[J] := (1 + X 1)*B - (1 + X 2)*A,
	have: C = X 1 ² - X 2 ²,
		change _*(_-_) - _*(_-_) = _,
		simp,
		ring,
	change _ ∈ spans[A,B],
	rw ←this,
	sorry
}