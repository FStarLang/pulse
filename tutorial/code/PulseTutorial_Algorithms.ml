open Prims
let rec read (p : unit) (s : unit)
  (arr : FStar_UInt32.t Pulse_Lib_Array_Core.array) (len : FStar_SizeT.t)
  (i : FStar_SizeT.t) : FStar_UInt32.t=
  Pulse_Lib_Array_Core.mask_read arr i () () ()
let rec majority :
  'a .
    unit ->
      unit ->
        'a Pulse_Lib_Array_Core.array ->
          FStar_SizeT.t -> 'a FStar_Pervasives_Native.option
  =
  fun p s votes len ->
    let i = Pulse_Lib_Reference.alloc () Stdint.Uint64.one in
    let k = Pulse_Lib_Reference.alloc () Stdint.Uint64.one in
    let votes_0 =
      Pulse_Lib_Array_Core.mask_read votes Stdint.Uint64.zero () () () in
    let cand = Pulse_Lib_Reference.alloc () votes_0 in
    Pulse_Lib_Dv.while_
      (fun while_cond ->
         let __anf0 = Pulse_Lib_Reference.read i () () in
         FStar_SizeT.lt __anf0 len)
      (fun while_body ->
         let vi = Pulse_Lib_Reference.read i () () in
         let vk = Pulse_Lib_Reference.read k () () in
         let vcand = Pulse_Lib_Reference.read cand () () in
         let votes_i = Pulse_Lib_Array_Core.mask_read votes vi () () () in
         if vk = Stdint.Uint64.zero
         then
           (Pulse_Lib_Reference.write cand votes_i;
            Pulse_Lib_Reference.write k Stdint.Uint64.one;
            Pulse_Lib_Reference.write i
              (FStar_SizeT.add vi Stdint.Uint64.one))
         else
           if votes_i = vcand
           then
             (Pulse_Lib_Reference.write k
                (FStar_SizeT.add vk Stdint.Uint64.one);
              Pulse_Lib_Reference.write i
                (FStar_SizeT.add vi Stdint.Uint64.one))
           else
             (Pulse_Lib_Reference.write k
                (FStar_SizeT.sub vk Stdint.Uint64.one);
              Pulse_Lib_Reference.write i
                (FStar_SizeT.add vi Stdint.Uint64.one)));
    (let vk = Pulse_Lib_Reference.read k () () in
     let vcand = Pulse_Lib_Reference.read cand () () in
     if vk = Stdint.Uint64.zero
     then FStar_Pervasives_Native.None
     else
       if FStar_SizeT.lt len (FStar_SizeT.mul (Stdint.Uint64.of_int (2)) vk)
       then FStar_Pervasives_Native.Some vcand
       else
         (Pulse_Lib_Reference.write i Stdint.Uint64.zero;
          Pulse_Lib_Reference.write k Stdint.Uint64.zero;
          Pulse_Lib_Dv.while_
            (fun while_cond ->
               let __anf0 = Pulse_Lib_Reference.read i () () in
               FStar_SizeT.lt __anf0 len)
            (fun while_body ->
               let vi = Pulse_Lib_Reference.read i () () in
               let vk1 = Pulse_Lib_Reference.read k () () in
               let votes_i = Pulse_Lib_Array_Core.mask_read votes vi () () () in
               if votes_i = vcand
               then
                 (Pulse_Lib_Reference.write k
                    (FStar_SizeT.add vk1 Stdint.Uint64.one);
                  Pulse_Lib_Reference.write i
                    (FStar_SizeT.add vi Stdint.Uint64.one))
               else
                 Pulse_Lib_Reference.write i
                   (FStar_SizeT.add vi Stdint.Uint64.one));
          (let vk1 = Pulse_Lib_Reference.read k () () in
           if
             FStar_SizeT.lt len
               (FStar_SizeT.mul (Stdint.Uint64.of_int (2)) vk1)
           then FStar_Pervasives_Native.Some vcand
           else FStar_Pervasives_Native.None)))
type u32_t = FStar_UInt32.t
let rec majority_mono (p : unit) (s : unit)
  (votes : u32_t Pulse_Lib_Array_Core.array) (len : FStar_SizeT.t) :
  u32_t FStar_Pervasives_Native.option= majority () () votes len
