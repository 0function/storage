import group_theory.coset ring_theory.matrix ring_theory.determinant ring_theory.ideals  algebra.gcd_domain algebra.euclidean_domain data.int.modeq group_theory.quotient_group data.equiv.algebra group_theory.subgroup
import tactic.ring tactic.fin_cases tactic.tidy
open function quotient_group group is_group_hom set classical
noncomputable theory

structure group_equiv (G H : Type*) [group G] [group H] extends G ≃ H :=
	(hom: is_group_hom to_fun)
	(inv_hom: is_group_hom inv_fun)
infix ` ≅ `:50 := group_equiv

namespace group_equiv
--I'd like not to repeat the Type*, but then there's an error with shadowing local universes.
variables{G:Type*}{H:Type*}{K:Type*}[group G][group H][group K]  {X:Type*}{Y:Type*}{Z:Type*}

instance: has_coe(G≅H)(G≃H) := ⟨λx,{..x}⟩

def via_biject_hom(f: G→H)(b: bijective f)(h: is_group_hom f): G ≅ H := {
	hom:=h,
	inv_hom:=⟨begin
		let E:= equiv.of_bijective b,
		let f:= E.to_fun,
		let g:= E.inv_fun,
		intros x y,
		change g(x*y) = g x * g y,
		have gf: ∀ a, g(f a) = a := E.left_inv,
		have fg: ∀ a, f(g a) = a := E.right_inv,
		rw[←gf(g x * g y)],
		apply congr_arg,
		have: f(g x * g y) = f(g x) * f(g y) := by apply h.mul,
		rw[this,fg,fg],
	end⟩,
	..equiv.of_bijective b
}

lemma bijective_comp{f:Y→Z}{g:X→Y}(bijf: bijective f)(bijg: bijective g): bijective(f∘g) :=begin
	constructor,
		{tidy},
	intro a,
	rcases bijf.right a with ⟨b, fb_a⟩,
	rcases bijg.right b with ⟨c, gc_b⟩,
	exact ⟨c,by simp;cc⟩,
end
protected def bijective(f: G ≅ H): bijective f := equiv.bijective f
instance(f: G≅H): is_group_hom f := f.hom

protected def refl: G ≅ G := via_biject_hom id (by simp[bijective,injective,surjective]) ⟨by simp⟩
protected def symm(f: G ≅ H): H ≅ G := {
	to_fun:= f.inv_fun,
	inv_fun:= f.to_fun,
	left_inv:= f.right_inv,
	right_inv:= f.left_inv,
	hom:= f.inv_hom,
	inv_hom:= f.hom,
}
protected def trans(gh: G ≅ H)(hk: H ≅ K): G ≅ K := via_biject_hom(hk ∘ gh) (bijective_comp hk.bijective gh.bijective) (by apply_instance) --infer_instance doesn't check

@[extensionality] lemma range_ext(f: X→Y)(x y ix iy)(x'y: x=y): (⟨x,ix⟩: range f) = ⟨y,iy⟩ := by simp[x'y]

--The first isomorphism theorem for groups. This one relates quotient to range, whereas the version below it avoids range assuming surjectivity.
def quotient_ker_isom_range(f: G→H)[is_group_hom f]: quotient(ker f) ≅ range f :=
	@via_biject_hom _ (range f) _ _
		(λ x, ⟨lift (ker f) f
  			(by simp [mem_ker]) x, by exact quotient.induction_on' x (λ x, ⟨x, rfl⟩)⟩)
  		⟨λ a b h, injective_ker_lift _ (subtype.mk.inj h),
  			λ ⟨x, y, hy⟩, ⟨quotient_group.mk y, subtype.eq hy⟩⟩
		⟨λx y, begin
			induction x,
			induction y,
			change (⟨quotient_group.lift (ker f) f _ (quotient_group.mk x * quotient_group.mk y), _⟩ : range f) = ⟨f x * f y, _⟩,
      ext,
		rw ←is_group_hom.mul f,
		repeat{refl},
		end⟩

def quotient_ker_isom_of_surjective(f: G→H)[is_group_hom f](s: surjective f): quotient(ker f) ≅ H :=
	(quotient_ker_isom_range f).trans(via_biject_hom subtype.val(begin
		constructor,
			{tidy},
		intro x,
		rcases s x with ⟨y, fy_x⟩,
		exact⟨⟨f y, by tidy⟩, by simpa⟩,
	end) (by tidy))
def isomorphism_theorem_1 := @quotient_ker_isom_range


--–1. attempt: use subsets (⟹ dead end)

def as_subset{A B: set X}(AsubB: A ⊆ B): set B := λb, A b
--Maximum class instance resolution depth gets continuously exceeded with this coercion...
instance coe_subset{B: set X}: has_coe(set X)(set B) := ⟨λA b, A b⟩
--...hence I package set under another name. This is for prototyping. Lifting all the definitions from set is inpractical, and a fixed type class inference should handle this IMO.
structure sub(T: Type*) := (base: set T)
namespace sub

instance: has_coe_to_sort(sub X) := {S:=Sort*, coe:=λs, (set.has_coe_to_sort.coe: set X → Sort _) s.base}
instance{B: sub X}: has_coe(sub X)(sub B) := ⟨λA, ⟨λb, A.base b⟩⟩

end sub

variables{M N S : sub G}[is_subgroup M.base][is_subgroup S.base][normal_subgroup N.base]

instance: is_subgroup((S: sub M).base) := {
	one_mem:= _inst_5.one_mem,
	mul_mem:=begin
		intros,
		have:= _inst_5.mul_mem,
		apply this a_1 a_2,
	end,
	inv_mem:=begin
		intros,
		have:= _inst_5.inv_mem,
		apply this a_1,
	end,
}
instance: normal_subgroup((N: sub M).base) := ⟨begin
	intros,
	change N.base(g*n*g⁻¹),
	have:= _inst_6.normal,
	apply this n _ g,
	apply H,
end⟩

--Result of these definitions: quotient between subgroups becomes defined.
@[reducible]def explicit_quotient(G:Type*)(N: sub G)[group G][normal_subgroup N.base] := quotient N.base
infix `∕`:70 := explicit_quotient
#check M∕N
--But quotients are not subtypes of each others of course.
--example[nM: normal_subgroup M.base](N_M: N.base ⊆ M.base): M∕N ⊆ G∕N


--–2. attempt: use embeddings with inference (⟹ too hard to infer)

--Embedding for sets
class embed(X Y : Type*) := (fn: X → Y)(inj: injective fn)
--To avoid non-termination, transitive closure must be build into another class, as in coe.lean. In general the rule is to take parameters of type embedₜ and produce instances of type embed.
class embedₜ(X Y : Type*) := (fn: X → Y)(inj: injective fn)
namespace embed

instance: has_coe_to_fun(embedₜ X Y) := {
	F:=λ_, X→Y,
	coe:= λi, i.fn
}
instance set{A: set X}: embed A X := {fn:=subtype.val, inj:= by tidy}

instance[i: embed X Y][j: embedₜ Y Z]: embedₜ X Z := {fn:= j.fn ∘ i.fn, inj:=begin
	have:= i.inj,
	have:= j.inj,
	tidy,
end}
--Note: It is very helpful to place the base case after the branch case for the inference engine!
instance base[i: embed X Y]: embedₜ X Y := {..i}

end embed

--Embedding for groups
class embed_group(G H : Type*)[group G][group H] extends embed G H := (hom: is_group_hom fn)
class embed_groupₜ(G H : Type*)[group G][group H] extends embedₜ G H := (hom: is_group_hom fn)
namespace embed_group
variables[i₁: embed_group G H][i: embed_groupₜ G H][j: embed_groupₜ H K]

instance set: embed_group S G := {hom:= by tidy, ..embed.set}

--Compare coe:X→Y and instance[X]:Y. Both are implicit conversions, but the first is for explicit terms whereas the second for implicit. Actually extends-declaration produces the second type of conversion:
example[embed_group G H]: embedₜ G H := infer_instance
--Explicit embeddings are supposed to be from the transitive closure, so coercion for them sufficies. Moreover lack of conversion for single step class can signal an error if ₜ is forgotten from a parameter (with unhelpful message).
instance: has_coe(embed_groupₜ G H)(embedₜ G H) := ⟨λi,{..i}⟩

instance: is_group_hom i := i.hom

--Problem: A definition may require a context with G⥅H and H⥅K, and then use the composed version. Assuming only G↪H in 1 step is generally too restrictive. I see no other way than to use explicit composition in this case.
def trans_comp(i: embed_groupₜ G H)(j: embed_groupₜ H K): embed_groupₜ G K :={
	fn:= j.fn ∘ i.fn,
	inj:=begin
		have:= i.inj,
		have:= j.inj,
		tidy,
	end,
	hom:= @is_group_hom.comp _ _ _ _ _ i.hom _ _ _ j.hom,
}

instance: embed_groupₜ G K := let _:=i₁ in trans_comp{..i₁}j
instance base: embed_groupₜ G H := {..i₁}

@[reducible]def quot_by_embed(H G : Type*)[group G][group H][i: embed_groupₜ G H] := quotient_group.quotient(range i)
infix `./ `:70 := quot_by_embed

def atomic_trans{R: embed_group G H → Sort*}(F: ∀[i₁: embed_group G H], R i₁)[i: embed_groupₜ G H] := @F{..i}

--Because the common assumption pair G ↪ₜ H ↪ₜ K doesn't chain automatically, the notation K./G can't be used.
private def K'G(i: embed_groupₜ G H)(j: embed_groupₜ H K) := @quot_by_embed K G _ _ (trans_comp i j)

def embed_and_quot_mk: H → K'G i j := @quotient_group.mk K _ (range(j∘i)) (by apply_instance) ∘ j

--If G is not normal, H/G is just a set and the lift for homomorphisms can't be used.
def nnlift(f: H → X)(h: ∀ a b, a⁻¹ * b ∈ range i → f a = f b): H./G → X := @quotient.lift _ _ (left_rel(range i)) f h

lemma embed_and_quot_mk_liftable: ∀ a b, a⁻¹ * b ∈ range i → embed_and_quot_mk a = (embed_and_quot_mk b : K'G i j)
:= let j:=j in begin
	intros,
	simp[embed_and_quot_mk],
	apply quotient_group.eq.mpr,
	change (j a)⁻¹ * j b ∈ range _,
	rw[←is_group_hom.inv j, ←is_group_hom.mul j],
	simp[has_mem.mem, set.mem, range],
	rcases a_1 with ⟨x, ix_a'b⟩,
	exact⟨x, by tidy⟩,
end

instance quot: embed(H./G)(K'G i j) := {
	fn:= nnlift embed_and_quot_mk embed_and_quot_mk_liftable,
	inj:= begin
		unfold injective,
		intros,
		induction a₁,
		induction a₂,
		apply quot.sound,
		change a₁⁻¹ * a₂ ∈ _,
		have: embed_and_quot_mk a₁ = embed_and_quot_mk a₂ := a,
		simp[embed_and_quot_mk] at this,
		have j_goal: (j a₁)⁻¹ * j a₂ ∈ range(j∘i) := (@quotient_group.eq K _ (range(j∘i)) _ (j a₁) (j a₂)).mp this,
		rw[←is_group_hom.inv j a₁, ←is_group_hom.mul j] at j_goal,
		rcases j_goal with ⟨x, e⟩,
		exact⟨x, begin apply j.inj, exact e end⟩,
	refl,refl,end,
}


--Next the normality is addied to the embeddings. Note that embed_normal is not an extension of embed_group but instead a property for it. This way it should be applicable to compositions of embeddings more flexibly.
class embed_normal(G H : Type*)[group G][group H][i: embed_groupₜ G H] := {normal: normal_subgroup(range i)}
--More explicit version.
@[reducible]def is_normal(i: embed_groupₜ G H) := @embed_normal G H _ _ i

variables[nj: embed_normal H K][nji: is_normal(trans_comp i j)]

instance[nj: is_normal j]: normal_subgroup(range j) := nj.normal
instance[nj: is_normal j]: group(K./H) := by apply_instance

instance comp_right_normal: is_normal i := {normal:=let _:=nji in ⟨begin
	intros,
	tactic.unfreeze_local_instances,
	rcases nji,
	have:= @normal_subgroup.normal K _ (range(j∘i)) nji (j n) _ (j g),
		rw[←is_group_hom.inv j, ←is_group_hom.mul j, ←is_group_hom.mul j] at this,
		rcases this with ⟨x, e⟩,
		simp at e,
		exact⟨x, begin apply j.inj, exact e end⟩,
	rcases H_1 with ⟨x,e⟩,
	exact⟨x, congr_arg j e⟩,
end⟩}

instance right_normal: normal_subgroup(range i) := (@embed_group.comp_right_normal G H K _ _ _ i j nji).normal

/-instance[i₁: embed_group G H][nji: is_normal(trans_comp (by apply_instance : embed_groupₜ G H) j)]: group(K./G) := begin
	have i: embed_groupₜ G H, apply_instance,
	have: normal_subgroup(range((trans_comp (by apply_instance : embed_groupₜ G H) j : embed_groupₜ G K) : G→K)), apply_instance,
		have:= @embed_group.normal_subgroup _ _ _ _ _ nji,
		rwa(_: j∘i = ((group_equiv.embed_groupₜ : embed_groupₜ _ _).fn : G→K)),
		have: embedₜ.fn K = j.fn ∘ i.fn,
			simp[embedₜ.fn],
end--/

instance right_group: group(@quot_by_embed H G _ _ i) := let _:=K,_:=j,_:=nji in begin
	have:= @embed_group.right_normal G H K _ _ _ i j nji,
	apply_instance,
end

instance group_K'G: group(K'G i j) :=let _:=nji in begin
	tactic.unfreeze_local_instances,
	rcases nji,
	exact @quotient_group.group K _inst_3 (range(j∘i)) nji,
end

instance hom_quot[nji: @embed_normal G K _ _ (trans_comp i j)]: embed_groupₜ(H./G)(K'G i j) := {
	hom:=⟨λa b, begin
		induction a,
		induction b,
		let f: H → H./G := quotient_group.mk,
		have: is_group_hom f, apply_instance,
		change embed.fn (K'G _ _) (f a * f b) = embed_group.embed_and_quot_mk a * embed_group.embed_and_quot_mk b,
		rw ←is_group_hom.mul f,
		change embed_group.embed_and_quot_mk _ = _,
		let f': K → _ := @quotient_group.mk K _ (range(j∘i)) (by apply_instance),
		tactic.unfreeze_local_instances,
		rcases nji,
		have nor: normal_subgroup(range(j∘i)) := nji,
		have gr: group(quotient(range(j∘i))) := (@quotient_group.group K _inst_3 (@range K G (⇑j ∘ ⇑i)) nor),
		have _hom_f' := @quotient_group.is_group_hom K _ _ nor,
		have: f' = @quotient_group.mk K _ (range(j∘i)) (by apply_instance) := rfl,
		rw←this at _hom_f',
		change f'(j(a*b)) = _,--f'(j a) * f'(j b),
		rw[is_group_hom.mul j],
		tidy,
	end⟩,
	..embed_group.quot
}

private def normal_mk(N: set G)(h: is_subgroup N)(prf): normal_subgroup N := {normal:= prf}

instance normal_quot[nj: embed_normal H K][nji: @embed_normal G K _ _ (trans_comp i j)]: embed_normal(H./G)(K'G i j):= {
	normal:=normal_mk
		(range((embed_group.hom_quot: embed_groupₜ (@quot_by_embed H G _ _ i) _): (@quot_by_embed H G _ _ i)→(K'G i j)))
		(begin
			have: is_group_hom((embed_group.hom_quot: embed_groupₜ (@quot_by_embed H G _ _ i) _): (@quot_by_embed H G _ _ i)→(K'G i j)),
				apply_instance,
			apply @is_group_hom.range_subgroup _ _ _ _ _ this,
		end)
		(begin
			intros,
			induction n,
			induction g,
			let f': K → K'G i j := @quotient_group.mk K _ (range(j∘i)) (by apply_instance),
			change f' g * f' n * (f' g)⁻¹ ∈ _,
			tactic.unfreeze_local_instances,
			rcases nji,
			have nor: normal_subgroup(range(j∘i)) := nji,
			let gr: group(quotient(range(j∘i))) := (@quotient_group.group K _inst_3 (@range K G (⇑j ∘ ⇑i)) nor),
			have _hom_f' := @quotient_group.is_group_hom K _ _ nor,
			have: f' = @quotient_group.mk K _ (range(j∘i)) (by apply_instance) := rfl,
			rw←this at _hom_f',
			have: gr = quotient_group.group(range(j∘i)) := rfl,
			simp[this] at *,
			rcases H_1 with ⟨⟨m⟩,e⟩,
			have e': f' n = f'(j m) := e.symm,
			rw e',
			rw[←@is_group_hom.mul _ _ _ _ f' _hom_f', ←@is_group_hom.inv _ _ _ _ f' _hom_f', ←@is_group_hom.mul _ _ _ _ f' _hom_f'],
			rcases nj.normal,
			rcases normal (j m) _ g with ⟨n',el⟩,
			exact⟨n', by tidy⟩,
			tidy,
		end)
}

end embed_group

open embed_group

/-The outcome of the attempt 2: class inference fails and the cause is very difficult to locate.
set_option trace.class_instances true
theorem isomorphism_theorem_3
	[j: embed_groupₜ H K]
	[embed_normal H K]
	[i: embed_group G H]
	[embed_normal G K]: --[@embed_normal G K _ _ (trans_comp i j)]:
		(K./G) ≅ K./H ∨
    true
    --(@quot_by_embed K G _ _ (trans_comp i j))./(H./G) ≅ K./H
	:= sorry
--/

end group_equiv

namespace group_equiv

--–3. attempt: embeddings with packing preferred over classes

structure Group := (base: Type*) (struct: group base)
variables{G: Group}{H: Group}{K: Group}

def 𝔾(G: Type*)[g: group G]: Group := ⟨G,g⟩

instance Group_to_Type: has_coe_to_sort Group := {S:=Type*, coe:= λG, G.base}
instance: group G := G.struct

structure group_homs(G H : Group) := (fn: G→H) (hom: is_group_hom fn)
infixr ` ⇒ ` := group_homs

instance homs_to_fun: has_coe_to_fun(group_homs G H) :={
	F:= λ_, G→ H,
	coe:= group_homs.fn
}

instance packed_is_group_hom{f: G⇒H}: is_group_hom f := f.hom

def compose(f: H⇒K)(g: G⇒H): G⇒K := ⟨f ∘ g, @is_group_hom.comp _ _ _ _ g g.hom _ _ f f.hom⟩

@[simp]lemma compose_fn(f: H⇒K)(g: G⇒H): (compose f g).fn = f.fn ∘ g.fn := rfl

--Is type class conditional coercion possible?
--instance sub_to_Group{S: set G}[is_subgroup S]: has_coe(set G)(Group) := ⟨λS, ⟨S, ??⟩⟩
def subGroup(S: set G)[is_subgroup S]: Group := ⟨S, infer_instance⟩

class embₜ(G H : Group) extends group_homs G H := (inj: injective fn)
class emb(G H : Group) extends group_homs G H := (inj: injective fn)--embₜ G H := unit --Prefer explicit instances so that base conversion can be ordered to be tried before transitivity.

namespace emb
variables[i₁: emb G H][i: embₜ G H][j: embₜ H K]

instance: has_coe(embₜ G H)(group_homs G H) := ⟨λi,{..i}⟩

instance sub{S: set G}[is_subgroup S]: emb (subGroup S) G := {hom:= by tidy, ..embed.set}

instance: embₜ G K := {
	fn:= j ∘ i₁.fn,
	inj:=begin
		have:= i₁.inj,
		have:= j.inj,
		tidy,
	end,
	hom:= @is_group_hom.comp _ _ _ _ _ i₁.hom _ _ _ j.hom,
}
instance base: embₜ G H := {..i₁}

instance: is_group_hom i := i.hom

class normally(G H : Group)[i: embₜ G H] := (normal: normal_subgroup(range i))

@[reducible]def quot_by_embed(H G : Group)[i: embₜ G H][normally G H]: Group := ⟨quotient_group.quotient(range i), begin
	have:= _inst_1.normal,
	apply @quotient_group.group _ _ _ this,
end⟩
infix `. ̸`:70 := quot_by_embed

instance[normally G H]: normal_subgroup(range i) := begin
	tactic.unfreeze_local_instances,
	rcases _inst_1,
	assumption,
end

protected def lift(f: H⇒K)(fG_1: ∀g, f(i g) = 1)[normally G H]: H. ̸G ⇒ K := let iG: set H := range i in ⟨@quotient_group.lift H H.struct iG _ K K.struct f f.hom (by tidy), @quotient_group.is_group_hom_quotient_lift H _ iG _ K _ f f.hom (by tidy)⟩

--When stating theorems e.g. here one wants to assume G ↪ͭ H ↪ͭ K both transitively and G ⊴ K which requires G ↪ͭ K to be inferred. This is impossible (I think). A workaround is to write helpers that assume G ↪¹ H in one step and then convert these to the desired form using atomic_trans.
def atomic_trans{R: emb G H → Sort*}(F: Πi₁: emb G H, R i₁)[i: embₜ G H] := F{..i}

def instance_normally(i₁: emb G H)[j: embₜ H K][normally G K]: normally G H :=⟨⟨begin
	intros,
	have:= _inst_1.normal.normal,
	have:= this(j n)(by tidy)(j g),
	rw[←is_group_hom.inv j,←is_group_hom.mul j,←is_group_hom.mul j] at this,
	rcases this with ⟨m,e⟩,
	exact⟨m, begin
		apply j.inj,
		apply e,
	end⟩,
end⟩⟩
instance:= @atomic_trans G H _ (@instance_normally G H K)

def instance_emb(i₁: emb G H)[j: embₜ H K][normally G K]: emb(H. ̸G)(K. ̸G) :={
	inj:=begin
		unfold injective,
		intros,
		induction a₁,
		induction a₂,
		apply quot.sound,
		have: quotient_group.mk(j a₁) = quotient_group.mk(j a₂) := a,
		change a₁⁻¹ * a₂ ∈ range _,
		have: j(a₁⁻¹ * a₂) ∈ range _,
			rw[is_group_hom.mul j, is_group_hom.inv j],
			simp[quotient_group.mk] at this,
			exact this,
		rcases this with ⟨g,e⟩,
		have ji:= j.inj, unfold injective at ji,
		exact⟨g, by tidy⟩,
	refl,refl,end,
	..emb.lift(compose (⟨quotient_group.mk, by apply_instance⟩: K⇒K. ̸G) {..j}) (λg,begin
		change (compose _ _).fn(i₁.fn g) = 1,
		simp,
		rw(_: (1:K. ̸G) = quotient_group.mk 1),
		apply eq.symm,
		apply quot.sound,
		change (1:K)⁻¹ * _ ∈ range _,
		tidy,
	end),
}
instance emb_quot_quot:= @atomic_trans G H _ (@instance_emb G H K)

def instance_emb_normal(i₁: emb G H)[j: embₜ H K][normally H K][normally G K]: normally(H. ̸G)(K. ̸G) := ⟨⟨begin
	intros,
	have: group K := K.struct,
	induction n,
	induction g,
	change quotient_group.mk _ * quotient_group.mk _ * (quotient_group.mk _)⁻¹ ∈ _,
	rw[←is_group_hom.inv(@quotient_group.mk K K.struct _ _),←is_group_hom.mul (@quotient_group.mk K K.struct _ _),←is_group_hom.mul (@quotient_group.mk K K.struct _ _)],
	rcases H_1 with ⟨x,e⟩,
	induction x,
	change quotient_group.mk _ = quotient_group.mk _ at e,
	simp[quotient_group.mk] at e,
	change _⁻¹ * n ∈ range _ at e,
	rcases e with ⟨m,h⟩,
	have ne: n = _ * _,
		apply inv_mul_eq_iff_eq_mul.mp,
		exact h.symm,
	change n = j x * j(i₁.fn m) at ne,
	rw[←is_group_hom.mul j] at ne,
	have:= _inst_1.normal.normal,
	rcases this n (by tidy) g,
	exact⟨quotient_group.mk w, begin
		change quotient_group.mk(j _) = _,
		apply congr_arg,
		exact h_1,
	end⟩,
	tidy,
end⟩⟩
instance normal_quot_quot:= @atomic_trans G H _ (@instance_emb_normal G H K)

end emb
open emb
open group_equiv

def quotient_preserves_isom{S N : set G}[normal_subgroup S][normal_subgroup N](SeN: S = N): quotient S ≅ quotient N := via_biject_hom
	(quotient_group.lift S quotient_group.mk (begin--well defined
		intros,
		tactic.unfreeze_local_instances,
		subst SeN,
		change _ = quotient_group.mk _,
		apply eq.symm,
		simp[quotient_group.mk],
		change _*x ∈ _,
		simpa,
	end))
	(begin--bijective
		tidy,
				change quotient_group.mk _ = quotient_group.mk _ at a,
				change quotient_group.mk _ = quotient_group.mk _,
				tactic.unfreeze_local_instances,
				subst SeN,
				apply a,
			exact quotient_group.mk b,
		refl,
	end)
	(by apply_instance)

private def f[emb G H][embₜ H K][normally H K][normally G K]: K. ̸G ⇒ K. ̸H :=
	emb.lift ⟨quotient_group.mk, by tidy⟩ begin
		intros,
		change quotient_group.mk _ = quotient_group.mk _,
		apply eq.symm,
		apply quot.sound,
		tidy,
	end

--The third isomorphism theorem. Use isomorphism_theorem_3 below that has the same type of quot_quot except that [embₜ G H] is inferred instead of explicit i₁. Unfortunately the type signature of isomorphism_theorem_3 can't be stated due to transitivity inference problems.
def quot_quot(i₁: emb G H)[j: embₜ H K][normally H K][normally G K]: (K. ̸G) . ̸ (H. ̸G) ≅ K. ̸H
:=begin
	have qk:= quotient_ker_isom_of_surjective f.fn (λx:K. ̸H, begin
		induction x,
		change ∃ y: K. ̸G, f.fn y = quotient_group.mk x,
		exact⟨quotient_group.mk x, begin
			simp[f, emb.lift],
			refl,
		end⟩,
		refl,
	end),
	let J: embₜ (H. ̸G) (K. ̸G) := infer_instance,
	have k: ker f.fn = range J,
		ext,
		induction x,
		simp[ker, f, emb.lift],
		change quotient_group.mk _ = quotient_group.mk _ ↔ _,
		have: (quotient_group.mk x = quotient_group.mk 1) = (quotient_group.mk 1 = quotient_group.mk x),
			ext, constructor; apply eq.symm,
		rw this,
		simp[quotient_group.mk],
		change _ * x ∈ _ ↔ _,
		simp,
		constructor;intro h; rcases h with ⟨y,jyx⟩,
			exact⟨quotient_group.mk y, begin
				rw←jyx,
				refl,
			end⟩,
		induction y,
		change quotient_group.mk _ = quotient_group.mk _ at jyx,
		simp[quotient_group.mk] at jyx,
		change _ * _ ∈ _ at jyx,
		rcases jyx with ⟨z,e⟩,
		have xe: x = _ * _,
			apply inv_mul_eq_iff_eq_mul.mp,
			exact e.symm,
		change x = j _ * j _ at xe,
		rw[←is_group_hom.mul j] at xe,
		exact⟨y*_, by rw xe;refl⟩,
		refl,refl,
	apply flip group_equiv.trans qk,
	change quotient_group.quotient _ ≅ _,
	have: is_subgroup(range J), apply_instance,
	have: is_subgroup(ker f.fn) := @is_group_hom.preimage (K. ̸G) (K. ̸H) _ _ f.fn f.hom (is_subgroup.trivial _) _,
	apply quotient_preserves_isom,
	apply k.symm,
	apply_instance,
	exact f.hom,
end
def isomorphism_theorem_3 := @atomic_trans G H _ (@quot_quot G H K)
#check @isomorphism_theorem_3

end group_equiv

/-Problem with evaluating this: basic examples are add_groups and I don't know how to transfer them into (multiplicative) groups.
namespace basic_embeddings
open group_equiv

instance ℤsubℚ: emb (𝔾 ℤ) (𝔾 ℚ)

end basic_embeddings
--/