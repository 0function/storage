import group_theory.coset ring_theory.matrix ring_theory.determinant ring_theory.ideals algebra.gcd_domain algebra.euclidean_domain data.int.modeq group_theory.quotient_group data.equiv.algebra group_theory.subgroup tactic.ring tactic.fin_cases tactic.tidy data.lazy_list category.monad.cont
open tactic native environment sum interactive lean.parser declaration binder_info interactive.types

meta instance: has_to_format binder_info := ⟨λi, match i with
| default := "def"
| implicit := "imp"
| strict_implicit := "IMP"
| inst_implicit := "iimp"
| aux_decl := "aux"
end⟩

meta def liikaako(m := 1) := do
	goals ← get_goals,
	if goals.length > m then do
		trace "Ylimääräisiä aliongelmia syntyi:", trace goals, failed
	else trace "—ei liikaa—"

def see{X}(x:X) := let _:= trace " • " X in trace "  ∋  " x

-----------------------------------------------------------------

universe U
--List monad (undeterminism) transformer has to be meta because of the recursion inside M. 
meta inductive search'(M: Type U → Type U)[monad M](X: Type U) : Type U
| stop : search'
| find : X → M search' → search'
@[reducible] meta def search(M)[monad M](X) := M(search' M X)
open search'
section variables{M: Type U → Type U}[monad M]{X: Type U}

def 𝓒{Y}(x:X)(y:Y) := x

meta def search.case{R}(stop': M R)(find': X → search M X → M R)(s: search M X): M R := do s←s, match s with
	| stop _ _ := stop'
	| find x s' := find' x s'
end

meta def pure_stop: search M X := @pure M _ _ (stop _ _)
meta def pure_find(x:X)(s: search M X) := @pure M _ _ (find x s)
infixr ` ;; `:66 := pure_find 
meta instance: has_emptyc(search M X) := ⟨pure_stop⟩

meta def headS: search M X → search M X |s:= s.case ∅ (𝓒∘(;;∅))

meta def mapS{R}(f: X → M R): search M X → search M R |s:= s.case ∅ (λx xs, f x >>= (;; mapS xs))

meta def appendS: search M X → search M X → search M X | s l := s.case l (λx xs, x ;; appendS xs l)

meta def joinS: search M (search M X) → search M X |s:= s.case ∅ (λl, appendS l ∘ joinS)

meta instance: has_pure(search M) := ⟨λ_, (;;∅)⟩
meta instance: has_bind(search M) := ⟨λ_ _ s f, joinS(mapS(pure∘f) s)⟩
meta instance: monad(search M) := {}

--Failure of M maps to ∅. 
meta def toS[alternative M](m: M X): search M X := @has_orelse.orelse M _ _ (flip find ∅ <$> m) ∅
end


section tactic_definitions

--Cool! This works (...alone—combined to e.g. string↝format it fails—for the tactic monad only)
meta def implicit_pure{T}: has_coe_to_fun T := {F:=𝓒(tactic T), coe:=pure}
local attribute [instance] implicit_pure
--notation `~ `:33 x := pure x
notation `ᵘᵖ ` m := monad_lift m

instance endomonoid{t}: monoid(t → t) := {
	one := id,
	mul := (∘),
	mul_assoc := function.comp.assoc,
	one_mul := function.comp.left_id,
	mul_one := function.comp.right_id,
}

def mrepeat{t m}[monad m](n:ℕ)(f: t → m t) := (fish f ^n) pure

--option.cases_on is theoretically more general, but its type matches in undesired way when used in conjunction with the tactic monad. 
def option.maybe{S T}(t)(st: S→T)(x: option S) := match x with none := t | some y := st y end

meta def name.decl(n) := do e ← get_env, e.get n
--Allow metavariables but don't add them as subgoals. 
meta def 𝔼(pre) := to_expr pre tt ff
meta def 𝔼ₙ(n) := get_local n <|> declaration.value<$>n.decl

meta def format_join{X}[has_to_tactic_format X](tstr: tactic format)(x: X) := do
	s ← tstr,
	xs ← pp x,
	pure(s++xs)
infixl ` ⧺ `:65 := format_join

meta def format_join'{X}[has_to_tactic_format X](tstr: tactic format)(xs: tactic(list X)) :=
	xs >>= list.foldl(λs x, s ⧺ "\n" ⧺ x) tstr
infixl ` -⧺ `:65 := format_join'

--TODO remove me after debugging
meta def infer_type'(e) := infer_type e <|> pure"infer_type: "⧺e >>= fail

meta def format_typed(e) := do
	t ← infer_type' e,
	pp e ⧺ "︓ " ⧺ t


meta instance: has_emptyc name_set := ⟨mk_name_set⟩
meta instance: has_insert name name_set := ⟨flip name_set.insert⟩
meta instance {T V}[has_lt T][decidable_rel((<):T→T→Prop)]: has_emptyc(rb_map T V) := ⟨rb_map.mk T V⟩
meta instance {T}[has_lt T][decidable_rel((<):T→T→Prop)]: has_emptyc(rb_set T) := ⟨rb_map.mk T unit⟩
meta instance{T}[has_lt T][decidable_rel((<):T→T→Prop)]: has_insert T (rb_set T) := ⟨λt S, rb_map.insert S t ()⟩

meta def trace_fail{X}(t: tactic X): tactic X := λs, match t s with
| interaction_monad.result.exception (some msg) _ s := failed(trace(msg()).to_string s)
| tac := tac
end
meta def trac{X}[has_to_tactic_format X](msg:string)(T: tactic X) := do t←T, trace(msg,t), t

meta def fold_names{T: Type*}(b:T)(f: name → expr → T → tactic T)(trust:=tt) := do
	e ← get_env,
	e.fold b (λd a,
		let n := d.to_name in
		if ¬n.is_internal ∧ d.is_trusted = trust then a >>= f n d.type else a)


--Problem 1: unspecialized meta variables in autoparameter target 
meta def a(n:ℕ) := do t←target>>=instantiate_mvars, trace(n,t), assumption
meta def a1:=a 1 meta def a2:=a 2 meta def a3:=a 3
meta def ta := target >>= trace >> assumption
def A(x:Type)(_:x. a1) := x
def B(x:Type)(_:x. a2) := x
def C(x:Type)(i:x)(_: A(B x)): A(B x) := i
def D(x:Type)(_:x. a1)(_:x. a2) := ℕ
def E(x:Type)(_:x): D x := nat.zero
--Problem 2: ∄ dynamic attributes
--Problem 3: rb_lmap is not reflected (can the instance be added?) ⇒ can't be used as attribute parameter
--The sorry can be used to mark branches that should be unreachable. This doesn't disturb the structure of the algorithm, and the place of an error is recorded for debugging. The same can't be achieved by tactic's fail, because the algorithm backtracks on some failures. The downside is that the algorithm can't be used outside its intented scope, because the caller can't recover from sorry either. 


meta def head_name: expr → name
| (expr.app f _) := head_name f
| (expr.const n _) := n
| (expr.local_const _ n _ _) := n --get_local doesn't handle unique names
| (expr.sort _) := "𝕊𝕆ℝ𝕋*"
| (expr.pi _ _ _ _) := "→"
| (expr.lam _ _ _ _) := "↦"
| _ := name.anonymous

meta def name's_type(n) := get_local_type n <|> type<$>n.decl

--This is to live with built-in inference. Testing i=inst_implicit would give better emulation. 
meta def takes_inst: expr → tactic bool | (expr.pi _ i s _) := is_class s.get_app_fn
|_:= sorry

meta def univ0(e: expr) := e.instantiate_univ_params(e.collect_univ_params.map(λn, (n, level.zero)))

meta def get_ps_types: expr → list(expr × binder_info)
| (expr.pi _ i s r) := (s,i) :: get_ps_types r
| _ := []

meta def result_type: expr → expr
| (expr.pi _ _ _ r) := result_type r
| r := r


meta structure inf_context := 
	(cache1: rb_lmap name name)
	(cache2: rb_lmap (name×name) name)
	(parent_hash: rb_set ℕ)
	(parent_tasks: list expr)

meta def empty_inf_state: inf_context := {
	cache1:= rb_lmap.mk name name, 
	cache2:= rb_lmap.mk (name×name) name, 
	parent_hash:={},
	parent_tasks:=[]}

/-This kind of caching looks promising, but it needs has_reflect instance. 
meta def persistent_cache_tag: user_attribute unit inf_context := {
	name:= `persistent_instance_cache,
	descr:= "Stores an updateable precomputed instance lookup table.",
	parser:= ~ empty_inf_state,
}--/

meta def let_reduced: expr → expr
| (expr.elet _ _ v b) := let_reduced(b.instantiate_var v)
| e := e

--Parameters: applied param.s (must be full), type of head, result acc.
meta def last_expl_par: list expr → expr → opt_param(option expr)none → expr
| (_::ps) (expr.pi _ _ `(auto_param %%_ %%_) r) ip := last_expl_par ps r ip
| (p::ps) (expr.pi _ default _ r) ip := last_expl_par ps r (some p)
| (_::ps) (expr.pi _ _ _ r) ip := last_expl_par ps r ip
| [] _ (some ip) := ip
| _ _ _ := sorry

--Non-existent name will be anonymous. Parameters in e need not be closed. 
meta def top_names(e: expr): tactic _ := do
	let (f,ps) := (let_reduced e).get_app_fn_args,
	prod.mk(head_name f)<$> head_name<$> last_expl_par ps <$> infer_type f


meta def initial_state: tactic inf_context := do
	let insertX := λ(S: inf_context) i t, (do
		(c,p) ← top_names t,
		pure(if p = name.anonymous 
		then {cache1:= S.cache1.insert c i, ..S}
		else {cache2:= S.cache2.insert(c,p) i, ..S})),
	ins ← attribute.get_instances `instance,
	S ← ins.reverse.mfoldl(λS i, name's_type i >>= insertX S i ∘ result_type) empty_inf_state,
	loc ← local_context >>= list.mfilter(λn, expr.get_app_fn <$> infer_type n >>= is_class),
	loc.mfoldl(λS i, infer_type i >>= insertX S (head_name i)) S


meta def applicable_laws(S: inf_context)(e) := do
	(c,p) ← instantiate_mvars e >>= top_names,
	let ls:= S.cache2.find(c,p) ++ S.cache1.find c,
	--pure"FOR  "⧺e⧺" <<"⧺c⧺", "⧺p⧺">>"-⧺ls⧺"\n" >>= trace,
	pure ls


--Expression that allows making fresh instances of itself.
private meta def expr' := tactic expr × expr

meta instance expr'_to_expr: has_coe expr' expr := ⟨prod.snd⟩
meta instance: has_to_tactic_format expr' := ⟨λe,pp(e:expr)⟩

meta def refresh: expr' → tactic expr' | (mkE,e) := trace("Refreshing ",e) >> prod.mk mkE <$> mkE

def mapi_help{S T}(f: ℕ → S → T): list T → ℕ → list S → list T
| r i [] := r
| r i (x::xs) := mapi_help (f i x :: r) (i+1) xs
def list.mapi{S T}(f: ℕ → S → T) := list.reverse ∘ mapi_help f [] 0

meta def map_freshable(f: expr → tactic(list expr)): expr' → tactic(list expr') | (mkE,e) := do
	fe ← f e,
	(fe.mapi(λi x, ((do 
		fe' ← mkE>>=f, 
		(fe'.nth i).iget), 
	x)))

--Return instance parameters reversed for better solving order (think dependences). 
meta def fresh_res_inst_ps: list expr → expr → tactic(expr × list expr) | ps e := do
	t ← infer_type e,
	match t with
	| expr.pi _ i s _ := do
		is_inst_param ← takes_inst t,
		e.app<$>mk_mvar >>= fresh_res_inst_ps(if is_inst_param then s::ps else ps)
	| r := (r,ps)
end

meta def requirements(law) := map_freshable(λe, do
	(r, ps) ← 𝔼ₙ law >>= fresh_res_inst_ps[],
	trace_fail(unify (univ0 r) (univ0 e) transparency.all),
	ps.mmap instantiate_mvars)


meta def pad_instance_params: list expr → expr → tactic(list(option expr))
| ps t@(expr.pi _ _ s r) := do
	i ← takes_inst t,
	pip ← pad_instance_params (ite i ps.tail ps) r,
	pip.cons(if i then some ps.head else none)
| [] _ := pure[]
| _ _ := sorry

--TODO cache (temporarily)
meta def build_instance(law)(ps: list _) := (do
	pps ← name's_type law >>= pad_instance_params ps.reverse,
	if pps=[] then resolve_name law >>= 𝔼 else mk_mapp law pps) <* trace("Success with law ",law)


meta def hash_ignore_mvars(e: expr) := e.fold 1 (λs _ h, nat.land 0xffFFffFF (31*h + match s with expr.const _ _ := s.hash  | _ := 1 end))

meta def childs(e: expr) := (e.mfoldl(λc s, [list.cons s c]) []).head

meta def equal_help: expr × expr → state(expr_map expr) bool
| (e, f@(expr.const _ _)) := pure(e = f)
-- | (e@(expr.mvar _ _ _), f@(expr.mvar _ _ _)) := do
-- 	vmap ← get,
-- 	when(¬ vmap.contains e) (put(vmap.insert e f)) 
-- 	$> (vmap.ifind e = f)
-- | (_, (expr.mvar _ _ _)) := pure ff
| (expr.mvar _ _ _, expr.mvar _ _ _) := pure tt --TODO why doesn't above “correct” definition work?
| (e, f) := let ec:= childs e, fc:= childs f in 
	if ec.length ≠ fc.length then pure ff else
		list.band <$> (ec.zip fc).mmap equal_help

meta def equal_ignore_mvars(e f) := ((equal_help(e,f)).run{}).fst

meta def get_def_locals(e: expr) := e.mfold [] (λs _ ls, match s with
	| expr.local_const _ _ _ _ := do s' ← whnf s, pure(if s' = s then ls else s::ls)
	| _ := ls end)


infixl ` ≫= `:55 := @has_bind.bind tactic _ _ _

meta def infer_class: inf_context → expr' → search tactic expr | S e :=
	let h := hash_ignore_mvars e in do toS$trace("infer_class",e,""),
	if S.parent_hash.contains h ∧ S.parent_tasks.any(equal_ignore_mvars e) then ∅
	else let S := {
		parent_hash:= S.parent_hash.insert h, 
		parent_tasks:= S.parent_tasks.cons e, 
	..S},
	try_instance(law e'): search tactic expr := do
		toS(trace("****** Applying ",law," to ",e')),
		rs ← toS(ᵘᵖ requirements law e'),
		toS(trace("OK, requirements ",rs.map(λk,(↑k:expr)))),
		rs.mmap(infer_class S) >>= toS ∘ build_instance law
	in
	applicable_laws S e ≫= λls, match ls with
		| [] := ∅
		| law::ls := (if expr.has_meta_var e then id else headS)
			(ls.foldl (λr l, appendS r ((ᵘᵖ refresh e) ≫= try_instance l)) (try_instance law e))
end

meta def get_instance_help(e: expr) := search.case (ᵘᵖ failed) (𝓒 ∘ pure) (initial_state ≫= flip infer_class(pure e, e))

meta def get_instance := do
	target >>= get_def_locals >>= revert_lst,
	whnf_target,
	t ← target,
	trace("::::::::::::::::::::::::::::::::::::::::::::: GOAL is ",t),
	let post := if t.has_meta_var then trace("Assumption solved ",t) else skip,
	assumption >> post <|> do
		`[try{rw auto_param_eq at *}],
		x ← get_instance_help t,
		exact x >> trace("-------------Solved ",t,"---------------")
		<|> pure"################# FAILED for "⧺t⧺"\n"⧺x⧺" is not valid instance" >>= fail


notation `✓ `C := auto_param C (name.mk_string "get_instance" name.anonymous)

lemma aceq{X}: (✓X) = X := rfl
meta def exact' (e : parse texpr) : tactic unit := do 
	`[rw aceq at *],
	tgt : expr ← target,
	i_to_expr_strict ``(%%e : %%tgt) >>= tactic.exact
run_cmd add_interactive ["exact'"]


meta def inst_head(n) := do 
	f ← expr.get_app_fn <$> result_type <$> name's_type n, 
	prod.mk f.const_name <$> get_expl_arity f
meta def count_ps(i): tactic ℕ := prod.snd <$> inst_head i

def counts{X}[decidable_eq X](s: list X) := s.erase_dup.map(λx, (x, (s.filter(=x)).length))

meta def expl_ps(e: expr): tactic(list expr) := do
	let (f,ps) := e.get_app_fn_args,
	ts ← get_ps_types <$> infer_type f,
	((ps.zip ts).filter(λ(p:_×_×_), p.snd.snd = default)).map prod.fst

meta def weird_head(e: expr) := match e.get_app_fn with
	| expr.const _ _ := ff
	| expr.var _ := ff
	| _ := tt
end


meta def koe := do
	E ← get_env,
	ins ← attribute.get_instances `instance,
	
	get_instance,
skip def use[add_group(ℕ×ℚ)]: add_group(ℚ×ℚ×ℚ) := by{
	let X:=ℚ, have: add_group(X×ℚ),
	revert X,
	-- whnf_target,
/-ö-/	koe,koe,
try{exact 1}}
end tactic_definitions
------------------------------------------------------------------------------
-- 3. isomorphism theorem as a test case --
------------------------------------------------------------------------------

namespace group_iso_test
open function quotient_group group is_group_hom set classical
noncomputable theory

structure group_equiv (G H : Type*) [group G] [group H] extends G ≃ H :=
	(hom: is_group_hom to_fun)
	(inv_hom: is_group_hom inv_fun)
infix ` ≅ `:50 := group_equiv

namespace group_equiv
--I'd like not to repeat the Type*, but then there's an error with shadowing local universes.
variables{G:Type}{H:Type}{K:Type}[group G][group H][group K]  {X:Type*}{Y:Type*}{Z:Type*}

@[priority std.priority.default+1] instance: has_coe(G≅H)(G≃H) := ⟨λx,{..x}⟩

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
protected def trans(gh: G ≅ H)(hk: H ≅ K): G ≅ K := via_biject_hom(hk ∘ gh) (bijective_comp hk.bijective gh.bijective) (by apply_instance) /-
infer_instance --/-- latter doesn't check -/

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


--–Embeddings with transitivity inferred by tactic--

--Set embedding
class embed(X Y : Type*) := (fn: X → Y)(inj: injective fn)
namespace embed

protected def trans(i: embed X Y)(j: embed Y Z): embed X Z := {fn:= j.fn ∘ i.fn, inj:=by{
	have:= i.inj,
	have:= j.inj,
	tidy,
}}

instance self: embed X X := {fn:= id, inj:= by tidy}
instance: has_coe_to_fun(embed X Y) := {F:=λ_, X→Y, coe:= λi, i.fn}
instance set{A: set X}: embed A X := {fn:=subtype.val, inj:= by tidy}

end embed


--Group embedding
class embed_group(G H : Type*)[group G][group H] extends embed G H := (hom: by exact is_group_hom fn)
namespace embed_group

--def auto_trans_embed_group(G H){_:✓ group G}[group H] := auto_param (embed_group G H) `get_instance
infixr `↪`:22 := embed_group

--@[transitivity] protected def trans(i: G↪H)(j: H↪K): G↪K :={
@[priority 0] instance trans{i: G↪H}{j: H↪K}: G↪K := {
	fn:= j.fn ∘ i.fn,
	inj:=begin
		have:= i.inj,
		have:= j.inj,
		tidy,
	end,
	hom:= @is_group_hom.comp _ _ _ _ _ i.hom _ _ _ j.hom,
}

instance self: G↪G := {hom:= ⟨by tidy⟩, ..embed.self}
instance set{S: set G}[is_subgroup S]: embed_group S G := {hom:= ⟨by tidy⟩, ..embed.set}
instance: has_coe(G↪H)(embed G H) := ⟨λi,{..i}⟩
instance(i:✓ G↪H): is_group_hom i := i.hom
instance(i:✓ G↪H): is_subgroup(range i) := @is_group_hom.range_subgroup _ _ _ _ i (embed_group.is_group_hom _)


@[reducible]def quot_by_embed(H G : Type)[group G][group H](i:✓ G↪H) := quotient_group.quotient(range i)
infix `∕`:70 := quot_by_embed

def embed_and_quot_mk{i:✓ G↪H}{j: H↪K}: H → K∕G := @quotient_group.mk _ _ _ embed_group.is_subgroup ∘ j

--If G is not normal, H/G is just a set and the lift for homomorphisms can't be used.
def nnlift{i: G↪H}(f: H → X)(h: ∀ a b, a⁻¹ * b ∈ range i → f a = f b): H∕G → X := @quotient.lift _ _ (left_rel(range i)) f h

lemma embed_and_quot_mk_liftable{i: G↪H}{j: H↪K}: ∀ a b, a⁻¹ * b ∈ range i → embed_and_quot_mk a = (embed_and_quot_mk b : K∕G)
:= begin
	intros,
	simp[embed_and_quot_mk],
	apply quotient_group.eq.mpr,
	change (j a)⁻¹ * j b ∈ range _,
	have h:= embed_group.is_group_hom j,
	rw[←@is_group_hom.inv _ _ _ _ _ h, ←@is_group_hom.mul _ _ _ _ _ h],
	simp[has_mem.mem, set.mem, range],
	rcases a_1 with ⟨x, ix_a'b⟩,
	exact⟨x, by tidy⟩,
end

instance quot{i: G↪H}{j: H↪K}: embed(H∕G)(K∕G) := {
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
		have h:= embed_group.is_group_hom j,
		rw[←@is_group_hom.inv _ _ _ _ _ h a₁, ←@is_group_hom.mul _ _ _ _ _ h] at j_goal,
		rcases j_goal with ⟨x, e⟩,
		exact⟨x, begin apply j.inj, exact e end⟩,
	refl,refl,end,
}

--Next the normality is added to the embeddings. Note that embed_normal is not an extension of embed_group but instead a property for it. This way it should be applicable to compositions of embeddings more flexibly.
class embed_normal(G H : Type)[group G][group H](i:✓ G↪H) := {normal: normal_subgroup(range i)}
infix `⊴`:50 := embed_normal

instance{i: G↪H}[ni: G⊴H]: normal_subgroup(range i) := ni.normal
@[priority std.priority.default+1] instance{i: G↪H}[ni: G⊴H]: group(H∕G) := by{
	change group(quotient_group.quotient _), 
	apply_instance,
}

instance right_normal{i: G↪H}{j: H↪K}[nji: G⊴K]: normal_subgroup(range i) := ⟨by{
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
}⟩

instance right_group{i: G↪H}{j: H↪K}[nj: H⊴K][nji: G⊴K]: group(H∕G) := begin
	have: normal_subgroup(range i) := @embed_group.right_normal G H K _ _ _ i j nji,
	apply_instance, --This uses right_normal!
end

instance group_K'G{i: G↪H}{j: H↪K}[nji: G⊴K]: group(K∕G) := begin
	tactic.unfreeze_local_instances,
	rcases nji,
	exact @quotient_group.group K _inst_3 (range(j∘i)) nji,
end

instance hom_quot{i: G↪H}{j: H↪K}[nj: H⊴K][nji: G⊴K]: H∕G ↪ K∕G := {
	hom:=⟨λa b, begin
		induction a,
		induction b,
		let f: H → H∕G := quotient_group.mk,
		have: is_group_hom f, apply_instance,
		change embed.fn (K∕G) (f a * f b) = embed_group.embed_and_quot_mk a * embed_group.embed_and_quot_mk b,
		rw ←is_group_hom.mul f,
		change embed_group.embed_and_quot_mk _ = _,
		let f': K → _ := @quotient_group.mk K _ (range(j∘i)) (embed_group.is_subgroup(@embed_group.trans _ _ _ _ _ _ i j)),
		tactic.unfreeze_local_instances,
		rcases nji,
		have nor: normal_subgroup(range(j∘i)) := nji,
		have gr: group(quotient(range(j∘i))) := (@quotient_group.group K _inst_3 (@range K G (⇑j ∘ ⇑i)) nor),
		have _hom_f' := @quotient_group.is_group_hom K _ _ nor,
		have: f' = @quotient_group.mk K _ (range(j∘i)) (by apply_instance) := rfl,
		rw←this at _hom_f',
		change f'(j(a*b)) = _,--f'(j a) * f'(j b),
		have h:= embed_group.is_group_hom j,
		rw[@is_group_hom.mul _ _ _ _ _ h],
		tidy,
	end⟩,
	..embed_group.quot
}

private def normal_mk(N: set G)(h: is_subgroup N)(prf): normal_subgroup N := {normal:= prf}

instance normal_quot{i: G↪H}{j: H↪K}[nj: H⊴K][nji: G⊴K]:
	let hg:=H∕G, kg:=K∕G in hg ⊴ kg := {
	normal:=normal_mk
		(range((embed_group.hom_quot: embed_group (@quot_by_embed H G _ _ i) _): (@quot_by_embed H G _ _ i)→(K∕G)))
		(begin
			have: is_group_hom((embed_group.hom_quot: H∕G ↪ K∕G): H∕G → K∕G),
				apply_instance,
			apply @is_group_hom.range_subgroup _ _ _ _ _ this,
		end)
		(begin
			intros,
			induction n,
			induction g,
			let f': K → K∕G := @quotient_group.mk K _ (range(j∘i)) (by apply_instance),
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

instance group_let{i: G↪H}{j: H↪K}[nj: H⊴K][nji: G⊴K]: let hg:=H∕G, kg:=K∕G in group(kg∕hg) := by{
	have:= @embed_group.normal_quot G H K _ _ _ _ _ nj _,
	simp at this,
	whnf_target, 
	apply @quotient_group.group _ _ _ this.normal,
}

end embed_group
open embed_group

structure group_homs(G H)[group G][group H] := (fn: G→H) (hom: is_group_hom fn)
infixr ` ⇒ ` := group_homs

instance homs_to_fun: has_coe_to_fun(group_homs G H) :={
	F:= λ_, G→ H,
	coe:= group_homs.fn
}

instance packed_is_group_hom{f: G⇒H}: is_group_hom f := f.hom

def compose(f: H⇒K)(g: G⇒H): G⇒K := ⟨f ∘ g, @is_group_hom.comp _ _ _ _ g g.hom _ _ f f.hom⟩

@[simp]lemma compose_fn(f: H⇒K)(g: G⇒H): (compose f g).fn = f.fn ∘ g.fn := rfl

def lift'h{i: G↪H}[ni: G⊴H](f: H⇒K)(fG_1: ∀g, f(i g) = 1): H∕G ⇒ K := let iG: set H := range i in ⟨@quotient_group.lift H (by apply_instance) iG ni.normal K _inst_3 f f.hom (by tidy), @quotient_group.is_group_hom_quotient_lift H _ iG ni.normal K _ f f.hom (by tidy)⟩

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


private def f[G↪H][H↪K][H⊴K][G⊴K]: K∕G ⇒ K∕H :=
	lift'h ⟨quotient_group.mk, by tidy⟩ begin
		intros,
		change quotient_group.mk _ = quotient_group.mk _,
		apply eq.symm,
		apply quot.sound,
		tidy,
	end


theorem isomorphism_theorem_3{i: G↪H}{j: H↪K}[nj: H⊴K][nji: G⊴K]: 
	let hg:=H∕G, kg:=K∕G in kg∕hg ≅ K∕H := by{

have qk:= quotient_ker_isom_of_surjective f.fn (λx:K∕H, begin
	induction x,
	change ∃ y: K∕G, f.fn y = quotient_group.mk x,
	exact⟨quotient_group.mk x, begin
		simp[f, lift'h],
		refl,
	end⟩,
	refl,
end),
let J: H∕G ↪ K∕G := infer_instance,
have k: ker f.fn = range J,
	ext,
	induction x,
	simp[ker, f, lift'h],
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
have: is_subgroup(ker f.fn) := @is_group_hom.preimage (K∕G) (K∕H) _ _ f.fn f.hom (is_subgroup.trivial _) _,
have: H∕G ⊴ K∕G, apply embed_group.normal_quot,
apply @quotient_preserves_isom _ _ _ _ this.normal (by apply_instance) k.symm,
apply_instance,
exact f.hom,
}


end group_equiv
end group_iso_test
---------------------------------------------------------------------------