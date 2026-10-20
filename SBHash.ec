require import AllCore List.

theory SBHash.

(* ================================================================ *)
(* SBHash: formal model of the FSB-inspired hash over F_5          *)
(* Concrete parameter set used in the paper                          *)
(* ================================================================ *)


op p   : int = 5.
op ell : int = 64.
op r   : int = 528.
op m   : int = 192.

(* Three F_5 coordinates are packed into one byte because
     5^3 = 125 < 256 < 625 = 5^4.
   Hence the 528-coordinate chaining state requires
     s = ceil(528 / 3) = 176
   alphabet symbols.
*)

op s : int = 176.

(* Number of fresh message symbols processed per compression call. *)
op q : int = 16.


(* ---------------------------------------------------------------- *)
(* Parameter consistency                                             *)
(* ---------------------------------------------------------------- *)

lemma p_value :
  p = 5.
proof.
  by smt().
qed.

lemma alphabet_size :
  ell * (p - 1) = 256.
proof.
  by smt().
qed.

lemma state_symbol_count :
  3 * (s - 1) < r /\ r <= 3 * s.
proof.
  by smt().
qed.

lemma round_input_decomposition :
  s + q = m.
proof.
  by smt().
qed.

lemma parameters_positive :
  0 < p /\ 0 < ell /\ 0 < r /\ 0 < m /\ 0 < s /\ 0 < q.
proof.
  by smt().
qed.

(* ---------------------------------------------------------------- *)
(* Concrete representation of F_5                                   *)
(* ---------------------------------------------------------------- *)

pred valid_fp (x : int) =
  0 <= x /\ x < p.

lemma valid_fp_bounds (x : int) :
  valid_fp x => 0 <= x /\ x <= 4.
proof.
  rewrite /valid_fp /p.
  smt().
qed.

lemma fp_zero_valid :
  valid_fp 0.
proof.
  rewrite /valid_fp /p.
  smt().
qed.

lemma fp_one_valid :
  valid_fp 1.
proof.
  rewrite /valid_fp /p.
  smt().
qed.


(* ---------------------------------------------------------------- *)
(* Alphabet A_ell = {0,...,ell-1} x F_5^*                           *)
(* ---------------------------------------------------------------- *)

type symbol = int * int.

op position (u : symbol) : int = u.`1.
op coefficient (u : symbol) : int = u.`2.

pred valid_symbol (u : symbol) =
  0 <= position u /\ position u < ell /\
  1 <= coefficient u /\ coefficient u < p.

lemma valid_symbol_position (u : symbol) :
  valid_symbol u =>
  0 <= position u /\ position u < 64.
proof.
  rewrite /valid_symbol /ell.
  smt().
qed.

lemma valid_symbol_coefficient (u : symbol) :
  valid_symbol u =>
  1 <= coefficient u /\ coefficient u <= 4.
proof.
  rewrite /valid_symbol /p.
  smt().
qed.


(* ---------------------------------------------------------------- *)
(* Byte-to-alphabet map                                              *)
(* b = 4j + (a-1)                                                    *)
(* ---------------------------------------------------------------- *)

op byte_of_symbol (u : symbol) : int =
  4 * position u + (coefficient u - 1).

lemma byte_of_valid_symbol_range (u : symbol) :
  valid_symbol u =>
  0 <= byte_of_symbol u /\ byte_of_symbol u < 256.
proof.
  rewrite /valid_symbol /byte_of_symbol /position /coefficient /ell /p.
  smt().
qed.

(* ---------------------------------------------------------------- *)
(* Byte decoding                                                     *)
(* ---------------------------------------------------------------- *)

pred valid_byte (b : int) =
  0 <= b /\ b < 256.


op symbol_of_byte : int -> symbol.

axiom symbol_of_byte_spec (b : int) :
  valid_byte b =>
  valid_symbol (symbol_of_byte b) /\
  byte_of_symbol (symbol_of_byte b) = b.

lemma symbol_of_valid_byte_is_valid (b : int) :
  valid_byte b =>
  valid_symbol (symbol_of_byte b).
proof.
  move=> Hb.
  have H := symbol_of_byte_spec b Hb.
  by smt().
qed.

lemma symbol_byte_inverse (b : int) :
  valid_byte b =>
  byte_of_symbol (symbol_of_byte b) = b.
proof.
  move=> Hb.
  have H := symbol_of_byte_spec b Hb.
  by smt().
qed.

lemma byte_encoding_injective (u v : symbol) :
  valid_symbol u =>
  valid_symbol v =>
  byte_of_symbol u = byte_of_symbol v =>
  u = v.
proof.
  case u => ju au.
  case v => jv av.

  rewrite /valid_symbol /byte_of_symbol
          /position /coefficient /ell /p.

  move=> Hu Hv Heq.

  have Hju : ju = jv by smt().
  have Hau : au = av by smt().

  by rewrite Hju Hau.
qed.

(* ---------------------------------------------------------------- *)
(* Packing three F_5 coordinates into one byte                      *)
(* ---------------------------------------------------------------- *)

op pack3 (u v w : int) : int =
  u + 5 * v + 25 * w.

pred valid_triple (u v w : int) =
  valid_fp u /\ valid_fp v /\ valid_fp w.

lemma pack3_range (u v w : int) :
  valid_triple u v w =>
  0 <= pack3 u v w /\ pack3 u v w < 125.
proof.
  rewrite /valid_triple /valid_fp /pack3 /p.
  smt().
qed.

lemma pack3_byte_range (u v w : int) :
  valid_triple u v w =>
  valid_byte (pack3 u v w).
proof.
  move=> H.
  have Hr := pack3_range u v w H.
  rewrite /valid_byte.
  smt().
qed.

lemma pack3_injective
  (u1 v1 w1 u2 v2 w2 : int) :
  valid_triple u1 v1 w1 =>
  valid_triple u2 v2 w2 =>
  pack3 u1 v1 w1 = pack3 u2 v2 w2 =>
  u1 = u2 /\ v1 = v2 /\ w1 = w2.
proof.
  rewrite /valid_triple /valid_fp /pack3 /p.
  smt().
qed.

(* ---------------------------------------------------------------- *)
(* Chaining-state representation                                     *)
(* ---------------------------------------------------------------- *)

type state = int list.

pred valid_state (x : state) =
  size x = r /\
  forall i, 0 <= i < r => valid_fp (nth 0 x i).

(* The packed state consists of s = 176 bytes. *)
type packed_state = int list.

pred valid_packed_state (y : packed_state) =
  size y = s /\
  forall i, 0 <= i < s => valid_byte (nth 0 y i).

(* Abstract state-packing function corresponding to the implementation:
   consecutive triples (u,v,w) are mapped to
      u + 5v + 25w,
   and the last incomplete triple is padded with zeros. *)

op pack_state : state -> packed_state.

axiom pack_state_valid (x : state) :
  valid_state x =>
  valid_packed_state (pack_state x).

axiom pack_state_injective (x y : state) :
  valid_state x =>
  valid_state y =>
  pack_state x = pack_state y =>
  x = y.

  (* ---------------------------------------------------------------- *)
(* State encoding into alphabet symbols                             *)
(* ---------------------------------------------------------------- *)

type encoded_state = symbol list.

pred valid_encoded_state (z : encoded_state) =
  size z = s /\
  forall i, 0 <= i < s => valid_symbol (nth (0,1) z i).


op encode_state_rec (x : state) : encoded_state =
  map symbol_of_byte (pack_state x).

lemma encode_state_rec_size
  (x : state) :
  valid_state x =>
  size (encode_state_rec x) = s.
proof.
  move=> Hx.

  have Hpack :
    valid_packed_state (pack_state x).
  - exact (pack_state_valid x Hx).

  rewrite /valid_packed_state in Hpack.

  rewrite /encode_state_rec.

  rewrite size_map.

  by smt().
qed.


lemma encode_state_rec_valid_symbols
  (x : state) :
  valid_state x =>
  forall i,
    0 <= i < s =>
    valid_symbol
      (nth (0,1) (encode_state_rec x) i).
proof.
  move=> Hx i Hi.

  have Hpack :
    valid_packed_state (pack_state x).
  - exact (pack_state_valid x Hx).

    rewrite /valid_packed_state in Hpack.

  move: Hpack => [Hpack_size Hpack_valid].

  have Hbyte :
    valid_byte (nth 0 (pack_state x) i).
  - exact (Hpack_valid i Hi).

 

  rewrite /encode_state_rec.

  rewrite (nth_map 0 (0,1) symbol_of_byte).
- by smt().

  exact
    (symbol_of_valid_byte_is_valid
       (nth 0 (pack_state x) i)
       Hbyte).
qed.

lemma encode_state_rec_spec
  (x : state) :
  valid_state x =>
  valid_encoded_state (encode_state_rec x).
proof.
  move=> Hx.

  rewrite /valid_encoded_state.

  split.

  - exact
      (encode_state_rec_size
         x Hx).

  - move=> i Hi.

    exact
      (encode_state_rec_valid_symbols
         x Hx i Hi).
qed.

op encode_state (x : state) : encoded_state =
  encode_state_rec x.

lemma encode_state_spec
  (x : state) :
  valid_state x =>
  valid_encoded_state (encode_state x).
proof.
  move=> Hx.

  rewrite /encode_state.

  exact
    (encode_state_rec_spec
       x Hx).
qed.

lemma encode_state_from_packed
  (x : state) :
  valid_state x =>
  forall i, 0 <= i < s =>
    nth (0,1) (encode_state x) i
    =
    symbol_of_byte (nth 0 (pack_state x) i).
proof.
  move=> Hx i Hi.

  have Hpack :
    valid_packed_state (pack_state x).
  - exact (pack_state_valid x Hx).

  rewrite /valid_packed_state in Hpack.

  move: Hpack => [Hsize Hvalid].

  rewrite /encode_state /encode_state_rec.

  rewrite (nth_map 0 (0,1) symbol_of_byte).

  - by smt().

  - trivial.
qed.

lemma encode_state_injective (x y : state) :
  valid_state x =>
  valid_state y =>
  encode_state x = encode_state y =>
  x = y.
proof.
  move=> Hx Hy Henc.

  apply (pack_state_injective x y Hx Hy).

  apply (List.eq_from_nth 0).

  - have [Vx_size Vx_valid] := pack_state_valid x Hx.
    have [Vy_size Vy_valid] := pack_state_valid y Hy.
    smt().

  - move=> i Hi.

    have [Vx_size Vx_valid] := pack_state_valid x Hx.
    have [Vy_size Vy_valid] := pack_state_valid y Hy.

    have HiS : 0 <= i < s by smt().

    have Ex := encode_state_from_packed x Hx i HiS.
    have Ey := encode_state_from_packed y Hy i HiS.

    rewrite Henc in Ex.

    have Bx := Vx_valid i HiS.
    have By := Vy_valid i HiS.

    have Hbx := symbol_byte_inverse
      (nth 0 (pack_state x) i) Bx.

    have Hby := symbol_byte_inverse
      (nth 0 (pack_state y) i) By.

    have Hsym :
      symbol_of_byte (nth 0 (pack_state x) i)
      =
      symbol_of_byte (nth 0 (pack_state y) i)
      by smt().

    by smt().
qed.

(* ---------------------------------------------------------------- *)
(* Fresh message block                                               *)
(* ---------------------------------------------------------------- *)

type msg_block = symbol list.

pred valid_msg_block (b : msg_block) =
  size b = q /\
  forall i, 0 <= i < q => valid_symbol (nth (0,1) b i).


(* ---------------------------------------------------------------- *)
(* Round input                                                       *)
(* U = Enc_st(x) || B                                                *)
(* ---------------------------------------------------------------- *)

type round_input = symbol list.

op make_round_input (x : state) (b : msg_block) : round_input =
  (encode_state x) ++ b.

pred valid_round_input (u : round_input) =
  size u = m /\
  forall i, 0 <= i < m => valid_symbol (nth (0,1) u i).


lemma round_input_length (x : state) (b : msg_block) :
  valid_state x =>
  valid_msg_block b =>
  size (make_round_input x b) = m.
proof.
  move=> Hx Hb.

  have Henc := encode_state_spec x Hx.

  rewrite /make_round_input.
  rewrite size_cat.

  have Hs : size (encode_state x) = s by smt().
  have Hq : size b = q by smt().

  smt(round_input_decomposition).
qed.


lemma make_round_input_valid (x : state) (b : msg_block) :
  valid_state x =>
  valid_msg_block b =>
  valid_round_input (make_round_input x b).
proof.
  move=> Hx Hb.

  rewrite /valid_round_input.

  split.

  - exact (round_input_length x b Hx Hb).

  - move=> i Hi.

    have [Henc_size Henc_valid] := encode_state_spec x Hx.
    have [Hb_size Hb_valid] := Hb.

    rewrite /make_round_input.

    case (i < s).

    + move=> His.

      have Hi_enc : 0 <= i < s by smt().
      have Henc_i := Henc_valid i Hi_enc.

      rewrite nth_cat.

      have Hsz : i < size (encode_state x) by smt().
      rewrite Hsz.

      exact Henc_i.

    + move=> Hnis.

      have Hib : 0 <= i - s < q
        by smt(round_input_decomposition).

      have Hb_i := Hb_valid (i - s) Hib.

      rewrite nth_cat.

      have Hsz : !(i < size (encode_state x)) by smt().
      rewrite Hsz.

      have Hidx :
        i - size (encode_state x) = i - s
        by smt().

      rewrite Hidx.

      exact Hb_i.
qed.

lemma make_round_input_injective
  (x y : state) (b1 b2 : msg_block) :
  valid_state x =>
  valid_state y =>
  valid_msg_block b1 =>
  valid_msg_block b2 =>
  make_round_input x b1 = make_round_input y b2 =>
  x = y /\ b1 = b2.
proof.
  move=> Hx Hy Hb1 Hb2 Heq.

  have Hencx := encode_state_spec x Hx.
  have Hency := encode_state_spec y Hy.

  have Hsx : size (encode_state x) = s by smt().
  have Hsy : size (encode_state y) = s by smt().

  have Henc_eq :
    encode_state x = encode_state y.
  + apply (List.eq_from_nth (0,1)).
    - smt().
    - move=> i Hi.

      have HiS : 0 <= i < s by smt().

      have Hleft :
        nth (0,1) (make_round_input x b1) i
        =
        nth (0,1) (encode_state x) i.
      + rewrite /make_round_input nth_cat.
        have Hlt : i < size (encode_state x) by smt().
        rewrite Hlt.
        trivial.

      have Hright :
        nth (0,1) (make_round_input y b2) i
        =
        nth (0,1) (encode_state y) i.
      + rewrite /make_round_input nth_cat.
        have Hlt : i < size (encode_state y) by smt().
        rewrite Hlt.
        trivial.

      rewrite -Hleft -Hright.
      by rewrite Heq.

  have Hxy : x = y.
  + exact (encode_state_injective x y Hx Hy Henc_eq).

  have Hb_eq :
    b1 = b2.
  + apply (List.eq_from_nth (0,1)).
    - smt().
    - move=> i Hi.

      have HiQ : 0 <= i < q by smt().

      have Hleft :
        nth (0,1) (make_round_input x b1) (s + i)
        =
        nth (0,1) b1 i.
      + rewrite /make_round_input nth_cat.
        have Hnot :
          !(s + i < size (encode_state x))
          by smt().
        rewrite Hnot.
        have Hidx :
          s + i - size (encode_state x) = i
          by smt().
        rewrite Hidx.
        trivial.

      have Hright :
        nth (0,1) (make_round_input y b2) (s + i)
        =
        nth (0,1) b2 i.
      + rewrite /make_round_input nth_cat.
        have Hnot :
          !(s + i < size (encode_state y))
          by smt().
        rewrite Hnot.
        have Hidx :
          s + i - size (encode_state y) = i
          by smt().
        rewrite Hidx.
        trivial.

      rewrite -Hleft -Hright.
      by rewrite Heq.

    split.
  - exact Hxy.
  - exact Hb_eq.
qed.


(* ---------------------------------------------------------------- *)
(* Compression function and round function                           *)
(* ---------------------------------------------------------------- *)

(* The compression function represents
       C(U) = H Phi(U)^T
   for a valid structured input U of m alphabet symbols.              *)

op compress : round_input -> state.

axiom compress_valid (u : round_input) :
  valid_round_input u =>
  valid_state (compress u).


(* One chaining round:
       F(x,B) = C( Enc_st(x) || B ).
*)

op round_function (x : state) (b : msg_block) : state =
  compress (make_round_input x b).


lemma round_function_valid (x : state) (b : msg_block) :
  valid_state x =>
  valid_msg_block b =>
  valid_state (round_function x b).
proof.
  move=> Hx Hb.

  rewrite /round_function.

  apply compress_valid.

  exact (make_round_input_valid x b Hx Hb).
qed.


(* ---------------------------------------------------------------- *)
(* Collision notions                                                 *)
(* ---------------------------------------------------------------- *)

pred compression_collision (u1 u2 : round_input) =
  valid_round_input u1 /\
  valid_round_input u2 /\
  u1 <> u2 /\
  compress u1 = compress u2.

pred round_collision
  (x1 x2 : state) (b1 b2 : msg_block) =
  valid_state x1 /\
  valid_state x2 /\
  valid_msg_block b1 /\
  valid_msg_block b2 /\
  (x1 <> x2 \/ b1 <> b2) /\
  round_function x1 b1 = round_function x2 b2.

lemma round_collision_implies_compression_collision
  (x1 x2 : state) (b1 b2 : msg_block) :
  round_collision x1 x2 b1 b2 =>
  compression_collision
    (make_round_input x1 b1)
    (make_round_input x2 b2).
proof.

  rewrite /round_collision /compression_collision.

  move=> [Hx1 [Hx2 [Hb1 [Hb2 [Hdiff Heq]]]]].

  split.

  - exact (make_round_input_valid x1 b1 Hx1 Hb1).

  split.

  - exact (make_round_input_valid x2 b2 Hx2 Hb2).

  split.

  - have Hinj :
      make_round_input x1 b1 = make_round_input x2 b2 =>
      x1 = x2 /\ b1 = b2.
    + exact
        (make_round_input_injective
          x1 x2 b1 b2
          Hx1 Hx2 Hb1 Hb2).

    smt().

  - rewrite /round_function in Heq.
    exact Heq.

qed.

(* ---------------------------------------------------------------- *)
(* Iterated construction                                             *)
(* ---------------------------------------------------------------- *)

type block_sequence = msg_block list.

pred valid_block_sequence (bs : block_sequence) =
  forall i, 0 <= i < size bs =>
    valid_msg_block (nth [] bs i).

(* Abstract recursive specification of the chaining process. *)

op iterate_rec (x : state) (bs : block_sequence) : state =
  with bs = []      => x
  with bs = b :: tl => iterate_rec (round_function x b) tl.

lemma iterate_rec_nil (x : state) :
  iterate_rec x [] = x.
proof.
  trivial.
qed.

lemma iterate_rec_cons
  (x : state) (b : msg_block) (bs : block_sequence) :
  iterate_rec x (b :: bs)
  =
  iterate_rec (round_function x b) bs.
proof.
  trivial.
qed.


op iterate (x : state) (bs : block_sequence) : state =
  iterate_rec x bs.

lemma iterate_nil (x : state) :
  iterate x [] = x.
proof.
  rewrite /iterate.
  exact (iterate_rec_nil x).
qed.

lemma iterate_cons
  (x : state) (b : msg_block) (bs : block_sequence) :
  iterate x (b :: bs)
  =
  iterate (round_function x b) bs.
proof.
  rewrite /iterate.
  exact (iterate_rec_cons x b bs).
qed.


(* ---------------------------------------------------------------- *)
(* Fixed initialization vector and complete iterated hash            *)
(* ---------------------------------------------------------------- *)

op iv : state.

axiom iv_valid :
  valid_state iv.

op hash_blocks (bs : block_sequence) : state =
  iterate iv bs.

(* ---------------------------------------------------------------- *)
(* Basic properties of the iterated hash                            *)
(* ---------------------------------------------------------------- *)

lemma hash_blocks_nil :
  hash_blocks [] = iv.
proof.
  rewrite /hash_blocks.
  exact (iterate_nil iv).
qed.


lemma hash_blocks_cons
  (b : msg_block) (bs : block_sequence) :
  hash_blocks (b :: bs)
  =
  iterate (round_function iv b) bs.
proof.
  rewrite /hash_blocks.
  exact (iterate_cons iv b bs).
qed.

(* ---------------------------------------------------------------- *)
(* Validity preservation through the iteration                      *)
(* ---------------------------------------------------------------- *)

lemma iterate_valid
  (x : state) (bs : block_sequence) :
  valid_state x =>
  valid_block_sequence bs =>
  valid_state (iterate x bs).
proof.
  elim bs x.

  (* Empty sequence *)
  - move=> x Hx Hbs.

    have Hnil :
      iterate x [] = x.
    + exact (iterate_nil x).

    by rewrite Hnil.

  (* Nonempty sequence *)
  - move=> b tl IH x Hx Hbs.

    have Hb :
      valid_msg_block b.
    + rewrite /valid_block_sequence in Hbs.

      have Hrange :
        0 <= 0 < size (b :: tl).
      * rewrite /=.
        have Hsz : 0 <= size tl.
        - exact (size_ge0 tl).
        smt().

      have H0 := Hbs 0 Hrange.

      rewrite /= in H0.

      exact H0.

    have Htl :
      valid_block_sequence tl.
    + rewrite /valid_block_sequence in Hbs.
      rewrite /valid_block_sequence.

      move=> i Hi.

      have Hrange :
        0 <= i + 1 < size (b :: tl).
      * rewrite /=.
        smt().

      have Hnext := Hbs (i + 1) Hrange.

      rewrite /= in Hnext.

      by smt().

    have Hnextstate :
      valid_state (round_function x b).
    + exact
        (round_function_valid
           x b
           Hx Hb).

    have Hcons :
      iterate x (b :: tl)
      =
      iterate (round_function x b) tl.
    + exact (iterate_cons x b tl).

    rewrite Hcons.

    exact
      (IH
         (round_function x b)
         Hnextstate
         Htl).
qed.


lemma hash_blocks_valid (bs : block_sequence) :
  valid_block_sequence bs =>
  valid_state (hash_blocks bs).
proof.
  move=> Hbs.

  rewrite /hash_blocks.

  exact (iterate_valid iv bs iv_valid Hbs).
qed.

(* ---------------------------------------------------------------- *)
(* Injective preprocessing / padding                                *)
(* ---------------------------------------------------------------- *)

type message.

op preprocess : message -> block_sequence.

axiom preprocess_valid (M : message) :
  valid_block_sequence (preprocess M).
pred aligned_suffix
  (xs ys : block_sequence) =
  size xs <= size ys /\
  forall t,
    0 <= t < size xs =>
    nth [] xs (size xs - 1 - t)
    =
    nth [] ys (size ys - 1 - t).

axiom preprocess_aligned_suffix_free
  (M1 M2 : message) :
  aligned_suffix
    (preprocess M1)
    (preprocess M2) =>
  M1 = M2.
lemma aligned_suffix_refl
  (bs : block_sequence) :
  aligned_suffix bs bs.
proof.
  rewrite /aligned_suffix.

  split.
  - by smt().

  - move=> t Ht.
    trivial.
qed.

lemma preprocess_injective_from_suffix
  (M1 M2 : message) :
  preprocess M1 = preprocess M2 =>
  M1 = M2.
proof.
  move=> Heq.

  have Hsuffix :
    aligned_suffix
      (preprocess M1)
      (preprocess M2).
  - rewrite Heq.
    exact
      (aligned_suffix_refl
         (preprocess M2)).

  exact
    (preprocess_aligned_suffix_free
       M1 M2 Hsuffix).
qed.

lemma preprocess_injective
  (M1 M2 : message) :
  preprocess M1 = preprocess M2 =>
  M1 = M2.
proof.
  exact
    (preprocess_injective_from_suffix
       M1 M2).
qed.

op hash_message (M : message) : state =
  hash_blocks (preprocess M).

(* ---------------------------------------------------------------- *)
(* Whole-hash collision notion                                      *)
(* ---------------------------------------------------------------- *)

pred hash_collision (M1 M2 : message) =
  M1 <> M2 /\
  hash_message M1 = hash_message M2.


(* Existence of a collision in one chaining round. *)

pred has_round_collision =
  exists (x1 x2 : state) (b1 b2 : msg_block),
    round_collision x1 x2 b1 b2.


(* Existence of a collision in the underlying compression function. *)

pred has_compression_collision =
  exists (u1 u2 : round_input),
    compression_collision u1 u2.

(* ---------------------------------------------------------------- *)
(* Equal-length whole-hash collisions                               *)
(* ---------------------------------------------------------------- *)

pred equal_length_hash_collision (M1 M2 : message) =
  hash_collision M1 M2 /\
  size (preprocess M1) = size (preprocess M2).

(* ---------------------------------------------------------------- *)
(* Chaining trace                                                    *)
(* ---------------------------------------------------------------- *)

op chain_state_rec
  (x : state) (bs : block_sequence) (i : int) : state =
  with bs = [] => x
  with bs = b :: tl =>
    if i <= 0 then x
    else
      chain_state_rec
        (round_function x b)
        tl
        (i - 1).


lemma chain_state_rec_zero
  (x : state) (bs : block_sequence) :
  chain_state_rec x bs 0 = x.
proof.
  case bs.

  - trivial.

  - move=> b tl.
    trivial.
qed.

lemma chain_state_rec_one
  (x : state) (b : msg_block) (bs : block_sequence) :
  chain_state_rec x (b :: bs) 1
  =
  round_function x b.
proof.
  have Hzero :
    chain_state_rec
      (round_function x b)
      bs
      0
    =
    round_function x b.
  - exact
      (chain_state_rec_zero
         (round_function x b)
         bs).

  by smt().
qed.

lemma chain_state_rec_succ
  (x : state) (b : msg_block) (bs : block_sequence) (i : int) :
  0 <= i =>
  chain_state_rec x (b :: bs) (i + 1)
  =
  chain_state_rec (round_function x b) bs i.
proof.
  move=> Hi.
  by smt().
qed.

lemma chain_state_rec_step
  (x : state) (bs : block_sequence) (i : int) :
  0 <= i < size bs =>
  chain_state_rec x bs (i + 1)
  =
  round_function
    (chain_state_rec x bs i)
    (nth [] bs i).
proof.
  move=> Hi.

  elim bs x i Hi.

  (* Impossible: empty sequence *)
  - move=> x i Hi.
    rewrite /= in Hi.
    by smt().

  (* Nonempty sequence *)
  - move=> b tl IH x i Hi.

    case (i = 0).

    + move=> Hiz.

      have Hleft :
        chain_state_rec x (b :: tl) (i + 1)
        =
        round_function x b.
      * rewrite Hiz.
        exact
          (chain_state_rec_one
             x b tl).

      have Hright_state :
        chain_state_rec x (b :: tl) i = x.
      * rewrite Hiz.
        exact
          (chain_state_rec_zero
             x
             (b :: tl)).

      have Hright_block :
        nth [] (b :: tl) i = b.
      * rewrite Hiz.
        trivial.

      by smt().

    + move=> Hine0.

      have HiPos :
        0 < i.
      * by smt().

      have HiMinus :
        0 <= i - 1 < size tl.
      * rewrite /= in Hi.
        by smt().

            have Hsucc1 :
        chain_state_rec x (b :: tl) (i + 1)
        =
        chain_state_rec
          (round_function x b)
          tl
          i.
      * have Htmp :=
          chain_state_rec_succ
            x b tl i.

        have HiNonneg :
          0 <= i.
        - by smt().

        exact (Htmp HiNonneg).

      have Hsucc0 :
        chain_state_rec x (b :: tl) i
        =
        chain_state_rec
          (round_function x b)
          tl
          (i - 1).
      * have Htmp :=
          chain_state_rec_succ
            x b tl (i - 1).
        have Hnonneg :
          0 <= i - 1.
        - by smt().
        have Heq :
          (i - 1) + 1 = i.
        - by smt().
        by smt().

      have HI :=
        IH
          (round_function x b)
          (i - 1)
          HiMinus.

      have Hnth :
        nth [] (b :: tl) i
        =
        nth [] tl (i - 1).
      * rewrite /=.
        by smt().

      by smt().
qed.

lemma chain_state_rec_final
  (x : state) (bs : block_sequence) :
  chain_state_rec x bs (size bs)
  =
  iterate x bs.
proof.
  elim bs x.

  (* Empty sequence *)
  - move=> x.

    have Hleft :
      chain_state_rec x [] 0 = x.
    + exact
        (chain_state_rec_zero
           x []).

    have Hright :
      iterate x [] = x.
    + exact (iterate_nil x).

    by smt().

  (* Nonempty sequence *)
  - move=> b tl IH x.

    have Hsz :
      0 <= size tl.
    + exact (size_ge0 tl).

    have Hstep :
      chain_state_rec x (b :: tl) (size tl + 1)
      =
      chain_state_rec
        (round_function x b)
        tl
        (size tl).
    + exact
        (chain_state_rec_succ
           x b tl
           (size tl)
           Hsz).

    have HI :
      chain_state_rec
        (round_function x b)
        tl
        (size tl)
      =
      iterate
        (round_function x b)
        tl.
    + exact
        (IH
           (round_function x b)).

    have Hiter :
      iterate x (b :: tl)
      =
      iterate
        (round_function x b)
        tl.
    + exact
        (iterate_cons x b tl).

    rewrite /=.

    by smt().
qed.

lemma chain_state_rec_valid
  (x : state) (bs : block_sequence) (i : int) :
  valid_state x =>
  valid_block_sequence bs =>
  0 <= i <= size bs =>
  valid_state (chain_state_rec x bs i).
proof.
  elim bs x i.

  (* Empty sequence *)
  - move=> x i Hx Hbs Hi.

    have Hiz :
      i = 0.
    + by smt().

    rewrite Hiz.

    have Hzero :
      chain_state_rec x [] 0 = x.
    + exact
        (chain_state_rec_zero
           x []).

    by rewrite Hzero.

  (* Nonempty sequence *)
  - move=> b tl IH x i Hx Hbs Hi.

    case (i = 0).

    (* Position 0: initial state *)
    + move=> Hiz.

      rewrite Hiz.
      exact Hx.

    (* Position i > 0 *)
    + move=> Hine0.

      have HiPos :
        0 < i.
      * by smt().

      have HiTail :
        0 <= i - 1 <= size tl.
      * by smt().    

      

      have Hb :
        valid_msg_block b.
      * rewrite /valid_block_sequence in Hbs.

        have Hrange :
          0 <= 0 < size (b :: tl).
        - rewrite /=.
          have Hsz :
            0 <= size tl.
          + exact (size_ge0 tl).
          smt().

        have H0 := Hbs 0 Hrange.

        exact H0.

      have Htl :
        valid_block_sequence tl.
      * rewrite /valid_block_sequence in Hbs.
        rewrite /valid_block_sequence.

        move=> j Hj.

        have Hrange :
          0 <= j + 1 < size (b :: tl).
        - rewrite /=.
          smt().

        have Hnext := Hbs (j + 1) Hrange.

        rewrite /= in Hnext.

        by smt().

      have Hnextstate :
        valid_state (round_function x b).
      * exact
          (round_function_valid
             x b
             Hx Hb).

      have Hrec :
        chain_state_rec x (b :: tl) i
        =
        chain_state_rec
          (round_function x b)
          tl
          (i - 1).
      * have Hnonneg :
          0 <= i - 1.
        - by smt().

        have Htmp :=
          chain_state_rec_succ
            x b tl
            (i - 1)
            Hnonneg.

        by smt().


            have Htailvalid :
        valid_state
          (chain_state_rec
             (round_function x b)
             tl
             (i - 1)).
      * exact
          (IH
             (round_function x b)
             (i - 1)
             Hnextstate
             Htl
             HiTail).

      by smt().
qed.

op chain_state
  (x : state) (bs : block_sequence) (i : int) : state =
  chain_state_rec x bs i.

lemma chain_state_zero
  (x : state) (bs : block_sequence) :
  chain_state x bs 0 = x.
proof.
  rewrite /chain_state.
  exact
    (chain_state_rec_zero
       x bs).
qed.

lemma chain_state_step
  (x : state) (bs : block_sequence) (i : int) :
  0 <= i < size bs =>
  chain_state x bs (i + 1)
  =
  round_function
    (chain_state x bs i)
    (nth [] bs i).
proof.
  move=> Hi.

  rewrite /chain_state.

  exact
    (chain_state_rec_step
       x bs i Hi).
qed.

lemma chain_state_final
  (x : state) (bs : block_sequence) :
  chain_state x bs (size bs)
  =
  iterate x bs.
proof.
  rewrite /chain_state.

  exact
    (chain_state_rec_final
       x bs).
qed.

(* Every state occurring along a valid chaining trace is valid. *)

lemma chain_state_valid
  (x : state) (bs : block_sequence) (i : int) :
  valid_state x =>
  valid_block_sequence bs =>
  0 <= i <= size bs =>
  valid_state (chain_state x bs i).
proof.
  move=> Hx Hbs Hi.

  rewrite /chain_state.

  exact
    (chain_state_rec_valid
       x bs i
       Hx
       Hbs
       Hi).
qed.

(* ---------------------------------------------------------------- *)
(* Helpers for valid block sequences                                *)
(* ---------------------------------------------------------------- *)

lemma valid_block_sequence_head
  (b : msg_block) (bs : block_sequence) :
  valid_block_sequence (b :: bs) =>
  valid_msg_block b.
proof.
  rewrite /valid_block_sequence.
  move=> H.

  have Hsz : 0 <= size bs.
  - exact (size_ge0 bs).

  have Hrange : 0 <= 0 < size (b :: bs).
  - rewrite /=.
    smt().

  have H0 := H 0 Hrange.

  rewrite /= in H0.

  exact H0.
qed.

lemma valid_block_sequence_tail
  (b : msg_block) (bs : block_sequence) :
  valid_block_sequence (b :: bs) =>
  valid_block_sequence bs.
proof.
  rewrite /valid_block_sequence.
  move=> H i Hi.

  have Hrange : 0 <= i + 1 < size (b :: bs).
  - rewrite /=.
    smt().

  have Hnext := H (i + 1) Hrange.

  rewrite /= in Hnext.

  by smt().
qed.

lemma equal_size_cons_tail
  (b1 b2 : msg_block)
  (bs1 bs2 : block_sequence) :
  size (b1 :: bs1) = size (b2 :: bs2) =>
  size bs1 = size bs2.
proof.
  rewrite /=.
  by smt().
qed.


lemma immediate_round_collision
  (x1 x2 : state) (b1 b2 : msg_block) :
  valid_state x1 =>
  valid_state x2 =>
  valid_msg_block b1 =>
  valid_msg_block b2 =>
  (x1 <> x2 \/ b1 <> b2) =>
  round_function x1 b1 = round_function x2 b2 =>
  has_round_collision.
proof.
  move=> Hx1 Hx2 Hb1 Hb2 Hdiff Heq.

  rewrite /has_round_collision.

  exists x1 x2 b1 b2.

  rewrite /round_collision.

  split.
  - exact Hx1.

  split.
  - exact Hx2.

  split.
  - exact Hb1.

  split.
  - exact Hb2.

  split.
  - exact Hdiff.
  - exact Heq.
qed.

lemma equal_length_iteration_collision
  (x1 x2 : state)
  (bs1 bs2 : block_sequence) :
  valid_state x1 =>
  valid_state x2 =>
  valid_block_sequence bs1 =>
  valid_block_sequence bs2 =>
  size bs1 = size bs2 =>
  iterate x1 bs1 = iterate x2 bs2 =>
  (x1 <> x2 \/ bs1 <> bs2) =>
  has_round_collision.
proof.
  elim bs1 x1 x2 bs2.

  (* ============================================================ *)
  (* Base case: bs1 = []                                         *)
  (* ============================================================ *)

  - move=> x1 x2 bs2 Hx1 Hx2 Hbs1.

    case bs2.

    (* ---------------------------------------------------------- *)
    (* bs1 = [] and bs2 = []                                     *)
    (* ---------------------------------------------------------- *)

    + move=> Hbs2 Hsize Heq Hdiff.

      have Hiter1 :
        iterate x1 [] = x1.
      * exact (iterate_nil x1).

      have Hiter2 :
        iterate x2 [] = x2.
      * exact (iterate_nil x2).

      have Hxeq :
        x1 = x2.
      * by smt().

      case Hdiff.

      * move=> Hxneq.
        by smt().

      * move=> Hnilneq.
        by smt().

    (* ---------------------------------------------------------- *)
    (* bs1 = [] and bs2 = b2 :: t2 : impossible by equal size    *)
    (* ---------------------------------------------------------- *)

    + move=> b2 t2 Hbs2 Hsize Heq Hdiff.

      rewrite /= in Hsize.

      have Hsz :
        0 <= size t2.
      * exact (size_ge0 t2).

      by smt().


  (* ============================================================ *)
  (* Inductive case: bs1 = b1 :: t1                              *)
  (* ============================================================ *)

  - move=> b1 t1 IH x1 x2 bs2 Hx1 Hx2 Hbs1.

    case bs2.

    (* ---------------------------------------------------------- *)
    (* bs1 nonempty and bs2 = [] : impossible by equal size      *)
    (* ---------------------------------------------------------- *)

    + move=> Hbs2 Hsize Heq Hdiff.

      rewrite /= in Hsize.

      have Hsz :
        0 <= size t1.
      * exact (size_ge0 t1).

      by smt().

    (* ---------------------------------------------------------- *)
    (* Both sequences are nonempty                               *)
    (* ---------------------------------------------------------- *)

    + move=> b2 t2 Hbs2 Hsize Heq Hdiff.

      have Hb1 :
        valid_msg_block b1.
      * exact
          (valid_block_sequence_head
             b1 t1 Hbs1).

      have Hb2 :
        valid_msg_block b2.
      * exact
          (valid_block_sequence_head
             b2 t2 Hbs2).

      have Ht1 :
        valid_block_sequence t1.
      * exact
          (valid_block_sequence_tail
             b1 t1 Hbs1).

      have Ht2 :
        valid_block_sequence t2.
      * exact
          (valid_block_sequence_tail
             b2 t2 Hbs2).

      have Htailsize :
        size t1 = size t2.
      * exact
          (equal_size_cons_tail
             b1 b2 t1 t2 Hsize).

      have Hy1 :
        valid_state (round_function x1 b1).
      * exact
          (round_function_valid
             x1 b1 Hx1 Hb1).

      have Hy2 :
        valid_state (round_function x2 b2).
      * exact
          (round_function_valid
             x2 b2 Hx2 Hb2).

      have Hiter1 :
        iterate x1 (b1 :: t1)
        =
        iterate (round_function x1 b1) t1.
      * exact (iterate_cons x1 b1 t1).

      have Hiter2 :
        iterate x2 (b2 :: t2)
        =
        iterate (round_function x2 b2) t2.
      * exact (iterate_cons x2 b2 t2).

      have Htaileq :
        iterate (round_function x1 b1) t1
        =
        iterate (round_function x2 b2) t2.
      * by smt().

      case (x1 <> x2 \/ b1 <> b2).

      (* -------------------------------------------------------- *)
      (* Current round inputs differ                              *)
      (* -------------------------------------------------------- *)

      * move=> Hcurrentdiff.

        case
          (round_function x1 b1
           =
           round_function x2 b2).

        (* They immediately merge: this is a round collision. *)

        + move=> Hroundeq.

          exact
            (immediate_round_collision
               x1 x2 b1 b2
               Hx1 Hx2 Hb1 Hb2
               Hcurrentdiff Hroundeq).

        (* Next states differ: recurse on the tails. *)

        + move=> Hroundneq.

          have Hnextdiff :
            round_function x1 b1
              <>
            round_function x2 b2
            \/
            t1 <> t2.
          * left.
            exact Hroundneq.

          exact
            (IH
               (round_function x1 b1)
               (round_function x2 b2)
               t2
               Hy1 Hy2
               Ht1 Ht2
               Htailsize
               Htaileq
               Hnextdiff).

      (* -------------------------------------------------------- *)
      (* Current round inputs are equal                           *)
      (* -------------------------------------------------------- *)

      * move=> Hcurrenteq.

        have Hx12 :
          x1 = x2.
        * by smt().

        have Hb12 :
          b1 = b2.
        * by smt().

        have Hroundeq :
          round_function x1 b1
          =
          round_function x2 b2.
        * by rewrite Hx12 Hb12.

        have Htailsdiff :
          t1 <> t2.
        * by smt().

        have Hnextdiff :
          round_function x1 b1
            <>
          round_function x2 b2
          \/
          t1 <> t2.
        * right.
          exact Htailsdiff.

        exact
          (IH
             (round_function x1 b1)
             (round_function x2 b2)
             t2
             Hy1 Hy2
             Ht1 Ht2
             Htailsize
             Htaileq
             Hnextdiff).
qed.

lemma equal_length_hash_collision_implies_round_collision
  (M1 M2 : message) :
  equal_length_hash_collision M1 M2 =>
  has_round_collision.
proof.
  rewrite /equal_length_hash_collision /hash_collision /hash_message.
  move=> [[Hneq Heq] Hsize].

  have Hpre1 :
    valid_block_sequence (preprocess M1).
  - exact (preprocess_valid M1).

  have Hpre2 :
    valid_block_sequence (preprocess M2).
  - exact (preprocess_valid M2).

  have Hseqneq :
    preprocess M1 <> preprocess M2.
  - have Hinj :
      preprocess M1 = preprocess M2 =>
      M1 = M2.
    + exact (preprocess_injective M1 M2).

    by smt().

  have Hdiff :
    iv <> iv \/ preprocess M1 <> preprocess M2.
  - right.
    exact Hseqneq.

  exact
    (equal_length_iteration_collision
       iv iv
       (preprocess M1)
       (preprocess M2)
       iv_valid
       iv_valid
       Hpre1
       Hpre2
       Hsize
       Heq
       Hdiff).
qed.

lemma equal_length_hash_collision_implies_compression_collision
  (M1 M2 : message) :
  equal_length_hash_collision M1 M2 =>
  has_compression_collision.
proof.
  move=> Hhash.

  have Hround :
    has_round_collision.
  - exact
      (equal_length_hash_collision_implies_round_collision
         M1 M2 Hhash).

  rewrite /has_round_collision in Hround.

  move: Hround =>
    [x1 x2 b1 b2 Hrc].

  rewrite /has_compression_collision.

  exists
    (make_round_input x1 b1)
    (make_round_input x2 b2).

  exact
    (round_collision_implies_compression_collision
       x1 x2 b1 b2 Hrc).
qed.

(* ---------------------------------------------------------------- *)
(* Length-strengthening / suffix-free preprocessing                  *)
(* ---------------------------------------------------------------- *)


(* ---------------------------------------------------------------- *)
(* Collision between two aligned trace positions                     *)
(* ---------------------------------------------------------------- *)

pred trace_round_collision
  (bs1 bs2 : block_sequence)
  (i j : int) =
  0 <= i < size bs1 /\
  0 <= j < size bs2 /\
  round_collision
    (chain_state iv bs1 i)
    (chain_state iv bs2 j)
    (nth [] bs1 i)
    (nth [] bs2 j).

lemma trace_round_collision_implies_has_round_collision
  (bs1 bs2 : block_sequence)
  (i j : int) :
  trace_round_collision bs1 bs2 i j =>
  has_round_collision.
proof.
  rewrite /trace_round_collision.
  move=> [Hi [Hj Hrc]].

  rewrite /has_round_collision.

  exists
    (chain_state iv bs1 i)
    (chain_state iv bs2 j)
    (nth [] bs1 i)
    (nth [] bs2 j).

  exact Hrc.
qed.

lemma chain_state_last_step
  (bs : block_sequence) :
  0 < size bs =>
  chain_state iv bs (size bs)
  =
  round_function
    (chain_state iv bs (size bs - 1))
    (nth [] bs (size bs - 1)).
proof.
  move=> Hpos.

  have Hidx :
    0 <= size bs - 1 < size bs.
  - by smt().

  have Hstep :=
    chain_state_step
      iv bs
      (size bs - 1)
      Hidx.

  have Hlast :
    (size bs - 1) + 1 = size bs.
  - by smt().

  by smt().
qed.

lemma equal_final_states_last_round
  (bs1 bs2 : block_sequence) :
  valid_block_sequence bs1 =>
  valid_block_sequence bs2 =>
  0 < size bs1 =>
  0 < size bs2 =>
  chain_state iv bs1 (size bs1)
  =
  chain_state iv bs2 (size bs2) =>
  trace_round_collision
    bs1 bs2
    (size bs1 - 1)
    (size bs2 - 1)
  \/
  (
    chain_state iv bs1 (size bs1 - 1)
    =
    chain_state iv bs2 (size bs2 - 1)
    /\
    nth [] bs1 (size bs1 - 1)
    =
    nth [] bs2 (size bs2 - 1)
  ).
proof.
  move=> Hbs1 Hbs2 Hpos1 Hpos2 Hfinal.

  have Hi1 :
    0 <= size bs1 - 1 < size bs1.
  - by smt().

  have Hi2 :
    0 <= size bs2 - 1 < size bs2.
  - by smt().

  have Hbound1 :
    0 <= size bs1 - 1 <= size bs1.
  - by smt().

  have Hbound2 :
    0 <= size bs2 - 1 <= size bs2.
  - by smt().

  have Hstate1 :
    valid_state
      (chain_state iv bs1 (size bs1 - 1)).
  - exact
      (chain_state_valid
         iv
         bs1
         (size bs1 - 1)
         iv_valid
         Hbs1
         Hbound1).

  have Hstate2 :
    valid_state
      (chain_state iv bs2 (size bs2 - 1)).
  - exact
      (chain_state_valid
         iv
         bs2
         (size bs2 - 1)
         iv_valid
         Hbs2
         Hbound2).

  have Hblock1 :
    valid_msg_block
      (nth [] bs1 (size bs1 - 1)).
  - exact
      (Hbs1
         (size bs1 - 1)
         Hi1).

  have Hblock2 :
    valid_msg_block
      (nth [] bs2 (size bs2 - 1)).
  - exact
      (Hbs2
         (size bs2 - 1)
         Hi2).

  have Hlast1 :=
    chain_state_last_step bs1 Hpos1.

  have Hlast2 :=
    chain_state_last_step bs2 Hpos2.

  have Hroundeq :
    round_function
      (chain_state iv bs1 (size bs1 - 1))
      (nth [] bs1 (size bs1 - 1))
    =
    round_function
      (chain_state iv bs2 (size bs2 - 1))
      (nth [] bs2 (size bs2 - 1)).
  - by smt().

  case (
    chain_state iv bs1 (size bs1 - 1)
      <>
    chain_state iv bs2 (size bs2 - 1)
    \/
    nth [] bs1 (size bs1 - 1)
      <>
    nth [] bs2 (size bs2 - 1)
  ).

  - move=> Hdiff.

    left.

    rewrite /trace_round_collision.

    split.
    + exact Hi1.

    split.
    + exact Hi2.

    rewrite /round_collision.

    split.
    + exact Hstate1.

    split.
    + exact Hstate2.

    split.
    + exact Hblock1.

    split.
    + exact Hblock2.

    split.
    + exact Hdiff.
    + exact Hroundeq.

  - move=> Hsame.

    right.

    split.
    + by smt().
    + by smt().
qed.

(* ---------------------------------------------------------------- *)
(* Preprocessing is nonempty                                        *)
(* ---------------------------------------------------------------- *)

lemma no_collision_implies_equal_last_inputs
  (bs1 bs2 : block_sequence) :
  valid_block_sequence bs1 =>
  valid_block_sequence bs2 =>
  0 < size bs1 =>
  0 < size bs2 =>
  chain_state iv bs1 (size bs1)
  =
  chain_state iv bs2 (size bs2) =>
  ! has_round_collision =>
  (
    chain_state iv bs1 (size bs1 - 1)
    =
    chain_state iv bs2 (size bs2 - 1)
    /\
    nth [] bs1 (size bs1 - 1)
    =
    nth [] bs2 (size bs2 - 1)
  ).
proof.
  move=> Hbs1 Hbs2 Hpos1 Hpos2 Hfinal Hno.

  have H :=
    equal_final_states_last_round
      bs1 bs2
      Hbs1 Hbs2
      Hpos1 Hpos2
      Hfinal.

  case H.

  - move=> Htrace.

    have Hround :
      has_round_collision.
    + exact
        (trace_round_collision_implies_has_round_collision
           bs1 bs2
           (size bs1 - 1)
           (size bs2 - 1)
           Htrace).

    by smt().

  - move=> Hequal.

    exact Hequal.
qed.

(* ---------------------------------------------------------------- *)
(* Matching suffix of two chaining traces                           *)
(* ---------------------------------------------------------------- *)

pred backward_match
  (bs1 bs2 : block_sequence)
  (k : int) =
  0 <= k /\
  k <= size bs1 /\
  k <= size bs2 /\
  chain_state iv bs1 (size bs1 - k)
  =
  chain_state iv bs2 (size bs2 - k)
  /\
  forall t,
    0 <= t < k =>
    nth [] bs1 (size bs1 - 1 - t)
    =
    nth [] bs2 (size bs2 - 1 - t).

lemma backward_match_zero
  (bs1 bs2 : block_sequence) :
  chain_state iv bs1 (size bs1)
  =
  chain_state iv bs2 (size bs2) =>
  backward_match bs1 bs2 0.
proof.
  move=> Hfinal.

  have Hsz1 :
    0 <= size bs1.
  - exact (size_ge0 bs1).

  have Hsz2 :
    0 <= size bs2.
  - exact (size_ge0 bs2).

  rewrite /backward_match.

  split.
  - by smt().

  split.
  - exact Hsz1.

  split.
  - exact Hsz2.

  split.
  - by smt().

  - move=> t Ht.
    by smt().
qed.


lemma backward_match_step
  (bs1 bs2 : block_sequence)
  (k : int) :
  valid_block_sequence bs1 =>
  valid_block_sequence bs2 =>
  backward_match bs1 bs2 k =>
  k < size bs1 =>
  k < size bs2 =>
  ! has_round_collision =>
  backward_match bs1 bs2 (k + 1).
proof.
  move=> Hbs1 Hbs2 Hmatch Hk1 Hk2 Hno.

  rewrite /backward_match in Hmatch.

  move: Hmatch =>
    [Hk0 [Hkle1 [Hkle2 [Hstate Hblocks]]]].

  have Hi1 :
    0 <= size bs1 - k - 1 < size bs1.
  - by smt().

  have Hi2 :
    0 <= size bs2 - k - 1 < size bs2.
  - by smt().

  have Hb1 :
    valid_msg_block
      (nth [] bs1 (size bs1 - k - 1)).
  - exact
      (Hbs1
         (size bs1 - k - 1)
         Hi1).

  have Hb2 :
    valid_msg_block
      (nth [] bs2 (size bs2 - k - 1)).
  - exact
      (Hbs2
         (size bs2 - k - 1)
         Hi2).

  have Hbound1 :
    0 <= size bs1 - k - 1 <= size bs1.
  - by smt().

  have Hbound2 :
    0 <= size bs2 - k - 1 <= size bs2.
  - by smt().

  have Hx1 :
    valid_state
      (chain_state iv bs1 (size bs1 - k - 1)).
  - exact
      (chain_state_valid
         iv
         bs1
         (size bs1 - k - 1)
         iv_valid
         Hbs1
         Hbound1).

  have Hx2 :
    valid_state
      (chain_state iv bs2 (size bs2 - k - 1)).
  - exact
      (chain_state_valid
         iv
         bs2
         (size bs2 - k - 1)
         iv_valid
         Hbs2
         Hbound2).

  have Hstep1 :=
    chain_state_step
      iv
      bs1
      (size bs1 - k - 1)
      Hi1.

  have Hstep2 :=
    chain_state_step
      iv
      bs2
      (size bs2 - k - 1)
      Hi2.

  have Hroundeq :
    round_function
      (chain_state iv bs1 (size bs1 - k - 1))
      (nth [] bs1 (size bs1 - k - 1))
    =
    round_function
      (chain_state iv bs2 (size bs2 - k - 1))
      (nth [] bs2 (size bs2 - k - 1)).
  - by smt().

  case (
    chain_state iv bs1 (size bs1 - k - 1)
      <>
    chain_state iv bs2 (size bs2 - k - 1)
    \/
    nth [] bs1 (size bs1 - k - 1)
      <>
    nth [] bs2 (size bs2 - k - 1)
  ).

  - move=> Hdiff.

    have Hrc :
      round_collision
        (chain_state iv bs1 (size bs1 - k - 1))
        (chain_state iv bs2 (size bs2 - k - 1))
        (nth [] bs1 (size bs1 - k - 1))
        (nth [] bs2 (size bs2 - k - 1)).
    + rewrite /round_collision.

      split.
      * exact Hx1.

      split.
      * exact Hx2.

      split.
      * exact Hb1.

      split.
      * exact Hb2.

      split.
      * exact Hdiff.
      * exact Hroundeq.

    have Hglobal :
      has_round_collision.
    + rewrite /has_round_collision.

      exists
        (chain_state iv bs1 (size bs1 - k - 1))
        (chain_state iv bs2 (size bs2 - k - 1))
        (nth [] bs1 (size bs1 - k - 1))
        (nth [] bs2 (size bs2 - k - 1)).

      exact Hrc.

    by smt().

  - move=> Hsame.

    have Hprev :
      chain_state iv bs1 (size bs1 - k - 1)
      =
      chain_state iv bs2 (size bs2 - k - 1).
    + by smt().

    have Hblock :
      nth [] bs1 (size bs1 - k - 1)
      =
      nth [] bs2 (size bs2 - k - 1).
    + by smt().

    rewrite /backward_match.

    split.
    + by smt().

    split.
    + by smt().

    split.
    + by smt().

    split.
    + by smt().

    move=> t Ht.

    case (t < k).

    + move=> Htk.

      have Htk_range :
        0 <= t < k.
      * by smt().

      exact
        (Hblocks t Htk_range).

    + move=> Hnot.

      have Htk :
        t = k.
      * by smt().

      by smt().
qed.

lemma backward_match_all
  (bs1 bs2 : block_sequence) :
  valid_block_sequence bs1 =>
  valid_block_sequence bs2 =>
  chain_state iv bs1 (size bs1)
  =
  chain_state iv bs2 (size bs2) =>
  ! has_round_collision =>
  forall k,
    0 <= k =>
    k <= size bs1 =>
    k <= size bs2 =>
    backward_match bs1 bs2 k.
proof.
  move=> Hbs1 Hbs2 Hfinal Hno.

  elim /intind.

  (* ------------------------------------------------------------ *)
  (* Base case: k = 0                                             *)
  (* ------------------------------------------------------------ *)

  - move=> Hle1 Hle2.

    exact
      (backward_match_zero
         bs1 bs2
         Hfinal).

  (* ------------------------------------------------------------ *)
  (* Induction step: k -> k + 1                                   *)
  (* ------------------------------------------------------------ *)

  - move=> k Hk IH Hnext1 Hnext2.

    have Hkle1 :
      k <= size bs1.
    + by smt().

    have Hkle2 :
      k <= size bs2.
    + by smt().

    have Hmatch :
      backward_match bs1 bs2 k.
    + exact
        (IH Hkle1 Hkle2).

    have Hlt1 :
      k < size bs1.
    + by smt().

    have Hlt2 :
      k < size bs2.
    + by smt().

    exact
      (backward_match_step
         bs1 bs2 k
         Hbs1 Hbs2
         Hmatch
         Hlt1 Hlt2
         Hno).
qed.

(* ---------------------------------------------------------------- *)
(* Indexed suffix relation                                          *)
(* ---------------------------------------------------------------- *)

lemma backward_match_full_shorter
  (bs1 bs2 : block_sequence) :
  size bs1 <= size bs2 =>
  backward_match bs1 bs2 (size bs1) =>
  aligned_suffix bs1 bs2.
proof.
  move=> Hsize Hmatch.

  rewrite /backward_match in Hmatch.

  move: Hmatch =>
    [Hk0 [Hkle1 [Hkle2 [Hstate Hblocks]]]].

  rewrite /aligned_suffix.

  split.

  - exact Hsize.

  - move=> t Ht.

    exact (Hblocks t Ht).
qed.

(* ---------------------------------------------------------------- *)
(* Suffix-freeness in indexed form                                  *)
(* ---------------------------------------------------------------- *)


lemma no_round_collision_forces_equal_messages_left_shorter
  (M1 M2 : message) :
  size (preprocess M1) <= size (preprocess M2) =>
  hash_message M1 = hash_message M2 =>
  ! has_round_collision =>
  M1 = M2.
proof.
  move=> Hsize Hhash Hno.

  have Hpre1 :
    valid_block_sequence (preprocess M1).
  - exact (preprocess_valid M1).

  have Hpre2 :
    valid_block_sequence (preprocess M2).
  - exact (preprocess_valid M2).

  have Hfinal :
    chain_state iv (preprocess M1) (size (preprocess M1))
    =
    chain_state iv (preprocess M2) (size (preprocess M2)).
  - have Hf1 :=
      chain_state_final
        iv
        (preprocess M1).

    have Hf2 :=
      chain_state_final
        iv
        (preprocess M2).

    rewrite /hash_message /hash_blocks in Hhash.

    by smt().

  have Hall :=
    backward_match_all
      (preprocess M1)
      (preprocess M2)
      Hpre1
      Hpre2
      Hfinal
      Hno.

  have Hsz1 :
    0 <= size (preprocess M1).
  - exact (size_ge0 (preprocess M1)).

  have Hself :
    size (preprocess M1) <= size (preprocess M1).
  - by smt().

  have Hmatch :
    backward_match
      (preprocess M1)
      (preprocess M2)
      (size (preprocess M1)).
  - exact
      (Hall
         (size (preprocess M1))
         Hsz1
         Hself
         Hsize).

  have Hsuffix :
    aligned_suffix
      (preprocess M1)
      (preprocess M2).
  - exact
      (backward_match_full_shorter
         (preprocess M1)
         (preprocess M2)
         Hsize
         Hmatch).

  exact
    (preprocess_aligned_suffix_free
       M1 M2 Hsuffix).
qed.

lemma no_round_collision_forces_equal_messages_right_shorter
  (M1 M2 : message) :
  size (preprocess M2) <= size (preprocess M1) =>
  hash_message M1 = hash_message M2 =>
  ! has_round_collision =>
  M1 = M2.
proof.
  move=> Hsize Hhash Hno.

  have Heq21 :
    hash_message M2 = hash_message M1.
  - by smt().

  have HM :
    M2 = M1.
  - exact
      (no_round_collision_forces_equal_messages_left_shorter
         M2 M1
         Hsize
         Heq21
         Hno).

  by smt().
qed.


lemma hash_collision_implies_round_collision
  (M1 M2 : message) :
  hash_collision M1 M2 =>
  has_round_collision.
proof.
  rewrite /hash_collision.
  move=> [Hneq Hhash].

  have Hem :
    has_round_collision \/ ! has_round_collision.
  - by smt().

  case Hem.

  (* ------------------------------------------------------------ *)
  (* A round collision already exists                             *)
  (* ------------------------------------------------------------ *)

  - move=> Hround.
    exact Hround.

  (* ------------------------------------------------------------ *)
  (* Assume no round collision exists                             *)
  (* ------------------------------------------------------------ *)

  - move=> Hno.

    case
      (size (preprocess M1)
       <=
       size (preprocess M2)).

    (* First preprocessing is shorter or equal. *)

    + move=> Hsize12.

      have Heq :
        M1 = M2.
      * apply
          (no_round_collision_forces_equal_messages_left_shorter
             M1 M2).

        - exact Hsize12.
        - exact Hhash.
        - exact Hno.

      by smt().

    (* Second preprocessing is shorter. *)

    + move=> Hnot12.

      have Hsize21 :
        size (preprocess M2)
        <=
        size (preprocess M1).
      * by smt().

      have Heq :
        M1 = M2.
      * apply
          (no_round_collision_forces_equal_messages_right_shorter
             M1 M2).

        - exact Hsize21.
        - exact Hhash.
        - exact Hno.

      by smt().
qed.


lemma hash_collision_implies_compression_collision
  (M1 M2 : message) :
  hash_collision M1 M2 =>
  has_compression_collision.
proof.
  move=> Hhash.

  have Hround :
    has_round_collision.
  - exact
      (hash_collision_implies_round_collision
         M1 M2 Hhash).

  rewrite /has_round_collision in Hround.

  move: Hround =>
    [x1 x2 b1 b2 Hrc].

  rewrite /has_compression_collision.

  exists
    (make_round_input x1 b1)
    (make_round_input x2 b2).

  exact
    (round_collision_implies_compression_collision
       x1 x2 b1 b2 Hrc).
qed.

end SBHash.