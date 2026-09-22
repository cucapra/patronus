- statebuffer / exprledge can be merged


SlotDataRef:
- reduce used to get baa::Value out the other end
- from_opaque_data: used in iterator, to make the get_data thing


requirements:
- hides type of internal pointer
- able to get a Baa::Value of some sort out of it ('reduction')

SlotDataRefMut:
- hides internal pointer type
- reduction
- 'unwrap' into a pointer of Word
- copy one data to another

---
compiler:
- make CodeGenContext builder-like: as in, another struct 'drives it' to add expressions and such
- do we really need to carry TaggedValue along with us everywhere?


expr_ctx:
- load_input_state: type, slot address associated with ExprRef
- input_state_slot: type, state offset
- expr_codegen: match based on type of expr, and potentially call load_input_staste / input_state_slot
  - otherwise knowing the type is enough
- dispatch_bv_operation_codegen: needed to get type


- apparently expr ordering doesn't really matter

analysis:
``find_leaf_states_upstream_dep``

codegen goes in order of walker


every codegen thing requires:
- expression content and its type
- input state slot address corresponding to the expr
  - use get_state_offset
- memory operations require more work
