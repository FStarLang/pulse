////
////
//// This file is generated by the Pulse2Rust tool
////
////

pub type sid_t = u16;
#[derive(Clone)]
pub struct session_state__Available__payload {
    pub context: super::dpetypes::context_t,
}
#[derive(Clone)]
pub enum session_state {
    SessionStart,
    Available(super::dpe::session_state__Available__payload),
    InUse,
    SessionClosed,
    SessionError,
}
pub type ht_t = super::pulse_lib_hashtable_type::ht_t<
    super::dpe::sid_t,
    super::dpe::session_state,
>;
pub struct st {
    pub st_ctr: super::dpe::sid_t,
    pub st_tbl: super::dpe::ht_t,
}
pub fn run_stt<A>(post: (), f: A) -> A {
    panic!()
}
pub fn sid_hash(s: super::dpe::sid_t) -> usize {
    s.into()
}
pub const fn initialize_global_state(
    uu___: (),
) -> ((), std::sync::Mutex<std::option::Option<super::dpe::st>>) {
    let m = std::sync::Mutex::new(None);
    ((), m)
}
pub static gst: ((), std::sync::Mutex<std::option::Option<super::dpe::st>>) = super::dpe::initialize_global_state(());
pub fn safe_incr(i: u16) -> std::option::Option<u16> {
    match i < 0xffff {
        true => Some(i + 1),
        _ => None,
    }
}
pub fn __open_session(
    s: super::dpe::st,
) -> (super::dpe::st, std::option::Option<super::dpe::sid_t>) {
    let ctr = s.st_ctr;
    let tbl = s.st_tbl;
    let copt = super::dpe::safe_incr(ctr);
    match copt {
        None => {
            let s1 = super::dpe::st {
                st_ctr: ctr,
                st_tbl: tbl,
            };
            let ret = (s1, None);
            ret
        }
        Some(mut ctr1) => {
            let ret = super::pulse_lib_hashtable::insert_if_not_full(
                tbl,
                ctr,
                super::dpe::session_state::SessionStart,
                (),
            );
            let tbl1 = ret.0;
            let b = ret.1;
            if b {
                let s1 = super::dpe::st {
                    st_ctr: ctr1,
                    st_tbl: tbl1,
                };
                let ret1 = (s1, Some(ctr));
                ret1
            } else {
                let s1 = super::dpe::st {
                    st_ctr: ctr,
                    st_tbl: tbl1,
                };
                let ret1 = (s1, None);
                ret1
            }
        }
    }
}
pub fn maybe_mk_session_tbl(
    sopt: std::option::Option<super::dpe::st>,
) -> super::dpe::st {
    match sopt {
        None => {
            let tbl = super::pulse_lib_hashtable::alloc(super::dpe::sid_hash, 256);
            let s = super::dpe::st {
                st_ctr: 0,
                st_tbl: tbl,
            };
            s
        }
        Some(mut s) => s,
    }
}
pub fn open_session(uu___: ()) -> std::option::Option<super::dpe::sid_t> {
    let mut mg = super::dpe::gst.1.lock().unwrap();
    let sopt = std::mem::replace::<std::option::Option<super::dpe::st>>(&mut mg, None);
    let s = super::dpe::maybe_mk_session_tbl(sopt);
    let ret = super::dpe::__open_session(s);
    let s1 = ret.0;
    let sid_opt = ret.1;
    *mg = Some(s1);
    std::mem::drop(mg);
    sid_opt
}
pub fn replace_session(
    sid: super::dpe::sid_t,
    t: (),
    sst: super::dpe::session_state,
    gsst: (),
) -> super::dpe::session_state {
    let mut mg = super::dpe::gst.1.lock().unwrap();
    let sopt = std::mem::replace::<std::option::Option<super::dpe::st>>(&mut mg, None);
    match sopt {
        None => panic!(),
        Some(mut s) => {
            let ctr = s.st_ctr;
            let tbl = s.st_tbl;
            if sid < ctr {
                let ret = super::pulse_lib_hashtable::lookup((), tbl, sid);
                let tbl1 = ret.0;
                let b = ret.1;
                let idx = ret.2;
                if b {
                    match idx {
                        Some(mut idx1) => {
                            let ret1 = super::pulse_lib_hashtable::replace(
                                (),
                                tbl1,
                                idx1,
                                sid,
                                sst,
                                (),
                            );
                            let tbl2 = ret1.0;
                            let st1 = ret1.1;
                            let s1 = super::dpe::st {
                                st_ctr: ctr,
                                st_tbl: tbl2,
                            };
                            *mg = Some(s1);
                            std::mem::drop(mg);
                            st1
                        }
                        None => panic!(),
                    }
                } else {
                    panic!()
                }
            } else {
                panic!()
            }
        }
    }
}
pub fn init_engine_ctxt(
    uds: &mut [u8],
    p: (),
    uds_bytes: (),
) -> super::dpetypes::context_t {
    let mut uds_buf = vec![0; super::enginetypes::uds_len];
    crate::pulse_lib_array::memcpy(
        super::enginetypes::uds_len,
        uds,
        &mut uds_buf,
        (),
        (),
        (),
    );
    let engine_context = super::dpetypes::mk_engine_context_t(uds_buf);
    let ctxt = super::dpetypes::mk_context_t_engine(engine_context);
    ctxt
}
pub fn initialize_context(
    sid: super::dpe::sid_t,
    t: (),
    p: (),
    uds_bytes: (),
    uds: &mut [u8],
) -> () {
    let s = super::dpe::replace_session(sid, (), super::dpe::session_state::InUse, ());
    match s {
        super::dpe::session_state::SessionStart => {
            let context = super::dpe::init_engine_ctxt(uds, (), ());
            let s1 = super::dpe::session_state::Available(super::dpe::session_state__Available__payload {
                context: context,
            });
            let s2 = super::dpe::replace_session(sid, (), s1, ());
        }
        super::dpe::session_state::InUse => panic!(),
        super::dpe::session_state::SessionClosed => panic!(),
        super::dpe::session_state::SessionError => panic!(),
        super::dpe::session_state::Available(_) => panic!(),
    }
}
pub fn init_l0_ctxt(
    cdi: &mut [u8],
    engine_repr: (),
    s: (),
    uds_bytes: (),
    uu___: (),
) -> super::dpetypes::l0_context_t {
    let mut cdi_buf = vec![0; 32];
    crate::pulse_lib_array::memcpy(32, cdi, &mut cdi_buf, (), (), ());
    let l0_context = super::dpetypes::mk_l0_context_t(cdi_buf);
    l0_context
}
pub fn init_l1_ctxt(
    cdi: (),
    deviceID_label_len: (),
    aliasKey_label_len: (),
    deviceIDCSR_ingredients: (),
    aliasKeyCRT_ingredients: (),
    deviceID_pub: std::vec::Vec<u8>,
    aliasKey_priv: std::vec::Vec<u8>,
    aliasKey_pub: std::vec::Vec<u8>,
    deviceIDCSR_len: u32,
    deviceIDCSR: std::vec::Vec<u8>,
    aliasKeyCRT_len: u32,
    aliasKeyCRT: std::vec::Vec<u8>,
    repr: (),
    deviceID_pub_repr: (),
    aliasKey_pub_repr: (),
    aliasKey_priv_repr: (),
    deviceIDCSR_repr: (),
    aliasKeyCRT_repr: (),
    uu___: (),
) -> super::dpetypes::l1_context_t {
    let ctxt = super::dpetypes::mk_l1_context_t(
        deviceID_pub,
        aliasKey_pub,
        aliasKey_priv,
        deviceIDCSR_len,
        deviceIDCSR,
        aliasKeyCRT_len,
        aliasKeyCRT,
    );
    ctxt
}
pub fn destroy_ctxt(ctxt: super::dpetypes::context_t, repr: ()) -> () {
    match ctxt {
        super::dpetypes::context_t::Engine_context(mut c) => drop(c.uds),
        super::dpetypes::context_t::L0_context(mut c) => drop(c.cdi),
        super::dpetypes::context_t::L1_context(mut c) => {
            drop(c.deviceID_pub);
            drop(c.aliasKey_priv);
            drop(c.aliasKey_pub);
            drop(c.aliasKeyCRT);
            drop(c.deviceIDCSR)
        }
    }
}
pub fn derive_child_from_context(
    context: super::dpetypes::context_t,
    record: super::dpetypes::record_t,
    record_repr: (),
    context_repr: (),
    uu___: (),
) -> std::option::Option<super::dpetypes::context_t> {
    match context {
        super::dpetypes::context_t::Engine_context(mut c) => {
            match record {
                super::dpetypes::record_t::Engine_record(mut r) => {
                    let cdi = &mut [0; 32];
                    let ret = super::enginecore::engine_main(
                        cdi,
                        &mut c.uds,
                        r,
                        (),
                        (),
                        (),
                        (),
                        (),
                    );
                    let r1 = ret.0;
                    super::dpe::destroy_ctxt(
                        super::dpetypes::context_t::Engine_context(c),
                        (),
                    );
                    let _bind_c = match ret.1 {
                        super::enginetypes::dice_return_code::DICE_SUCCESS => {
                            let l0_ctxt = super::dpe::init_l0_ctxt(cdi, (), (), (), ());
                            let ret1 = Some(
                                super::dpetypes::context_t::L0_context(l0_ctxt),
                            );
                            ret1
                        }
                        super::enginetypes::dice_return_code::DICE_ERROR => {
                            crate::pulse_lib_array::zeroize(32, cdi, ());
                            let ret1 = None;
                            ret1
                        }
                    };
                    let cdi1 = _bind_c;
                    cdi1
                }
                super::dpetypes::record_t::L0_record(_) => panic!(),
            }
        }
        super::dpetypes::context_t::L0_context(mut c) => {
            match record {
                super::dpetypes::record_t::L0_record(mut r) => {
                    let mut deviceID_pub = vec![0; 32];
                    let mut aliasKey_pub = vec![0; 32];
                    let mut aliasKey_priv = vec![0; 32];
                    let deviceIDCSR_len = super::l0types::len_of_deviceIDCSR(
                        r.deviceIDCSR_ingredients,
                    );
                    let aliasKeyCRT_len = super::l0types::len_of_aliasKeyCRT(
                        r.aliasKeyCRT_ingredients,
                    );
                    let mut deviceIDCSR = vec![
                        0; crate ::fstar_sizet::uint32_to_sizet(deviceIDCSR_len)
                    ];
                    let mut aliasKeyCRT = vec![
                        0; crate ::fstar_sizet::uint32_to_sizet(aliasKeyCRT_len)
                    ];
                    crate::l0core::l0(
                        &mut c.cdi,
                        &mut r.fwid,
                        r.deviceID_label_len,
                        &mut r.deviceID_label,
                        r.aliasKey_label_len,
                        &mut r.aliasKey_label,
                        r.deviceIDCSR_ingredients,
                        r.aliasKeyCRT_ingredients,
                        &mut deviceID_pub,
                        &mut aliasKey_pub,
                        &mut aliasKey_priv,
                        deviceIDCSR_len,
                        &mut deviceIDCSR,
                        aliasKeyCRT_len,
                        &mut aliasKeyCRT,
                        (),
                        (),
                        (),
                        (),
                        (),
                        (),
                        (),
                        (),
                        (),
                    );
                    let l1_context = super::dpe::init_l1_ctxt(
                        (),
                        (),
                        (),
                        (),
                        (),
                        deviceID_pub,
                        aliasKey_priv,
                        aliasKey_pub,
                        deviceIDCSR_len,
                        deviceIDCSR,
                        aliasKeyCRT_len,
                        aliasKeyCRT,
                        (),
                        (),
                        (),
                        (),
                        (),
                        (),
                        (),
                    );
                    super::dpe::destroy_ctxt(
                        super::dpetypes::context_t::L0_context(c),
                        (),
                    );
                    let ret = Some(super::dpetypes::context_t::L1_context(l1_context));
                    ret
                }
                super::dpetypes::record_t::Engine_record(_) => panic!(),
            }
        }
        super::dpetypes::context_t::L1_context(_) => panic!(),
    }
}
pub fn derive_child(
    sid: super::dpe::sid_t,
    t: (),
    record: super::dpetypes::record_t,
    rrepr: (),
) -> bool {
    let s = super::dpe::replace_session(sid, (), super::dpe::session_state::InUse, ());
    match s {
        super::dpe::session_state::Available(mut hc) => {
            match hc.context {
                super::dpetypes::context_t::L1_context(_) => panic!(),
                _ => {
                    let ret = super::dpe::derive_child_from_context(
                        hc.context,
                        record,
                        (),
                        (),
                        (),
                    );
                    match ret {
                        Some(mut nctxt) => {
                            let s1 = super::dpe::session_state::Available(super::dpe::session_state__Available__payload {
                                context: nctxt,
                            });
                            let s2 = super::dpe::replace_session(sid, (), s1, ());
                            true
                        }
                        None => {
                            let s1 = super::dpe::session_state::SessionError;
                            let s2 = super::dpe::replace_session(sid, (), s1, ());
                            false
                        }
                    }
                }
            }
        }
        super::dpe::session_state::SessionStart => panic!(),
        super::dpe::session_state::InUse => panic!(),
        super::dpe::session_state::SessionClosed => panic!(),
        super::dpe::session_state::SessionError => panic!(),
    }
}
pub fn destroy_session_state(s: super::dpe::session_state, t: ()) -> () {
    match s {
        super::dpe::session_state::Available(mut hc) => {
            super::dpe::destroy_ctxt(hc.context, ())
        }
        _ => {}
    }
}
pub fn close_session(sid: super::dpe::sid_t, t: ()) -> () {
    let s = super::dpe::replace_session(sid, (), super::dpe::session_state::InUse, ());
    super::dpe::destroy_session_state(s, ());
    let s1 = super::dpe::replace_session(
        sid,
        (),
        super::dpe::session_state::SessionClosed,
        (),
    );
}
pub fn certify_key(
    sid: super::dpe::sid_t,
    pub_key: &mut [u8],
    crt_len: u32,
    crt: &mut [u8],
    t: (),
) -> u32 {
    let s = super::dpe::replace_session(sid, (), super::dpe::session_state::InUse, ());
    match s {
        super::dpe::session_state::Available(mut hc) => {
            match hc.context {
                super::dpetypes::context_t::L1_context(mut c) => {
                    let c_crt_len = c.aliasKeyCRT_len;
                    if crt_len < c_crt_len {
                        let ns = super::dpe::session_state::Available(super::dpe::session_state__Available__payload {
                            context: super::dpetypes::context_t::L1_context(c),
                        });
                        let s1 = super::dpe::replace_session(sid, (), ns, ());
                        0
                    } else {
                        crate::pulse_lib_array::memcpy_l(
                            32,
                            &mut c.aliasKey_pub,
                            pub_key,
                            (),
                            (),
                            (),
                        );
                        crate::pulse_lib_array::memcpy_l(
                            crate::fstar_sizet::uint32_to_sizet(c.aliasKeyCRT_len),
                            &mut c.aliasKeyCRT,
                            crt,
                            (),
                            (),
                            (),
                        );
                        let ns = super::dpe::session_state::Available(super::dpe::session_state__Available__payload {
                            context: super::dpetypes::context_t::L1_context(c),
                        });
                        let s1 = super::dpe::replace_session(sid, (), ns, ());
                        c_crt_len
                    }
                }
                _ => panic!(),
            }
        }
        _ => panic!(),
    }
}
pub fn sign(
    sid: super::dpe::sid_t,
    signature: &mut [u8],
    msg_len: usize,
    msg: &mut [u8],
    t: (),
) -> () {
    let s = super::dpe::replace_session(sid, (), super::dpe::session_state::InUse, ());
    match s {
        super::dpe::session_state::Available(mut hc) => {
            match hc.context {
                super::dpetypes::context_t::L1_context(mut c) => {
                    super::hacl::ed25519_sign(
                        signature,
                        &mut c.aliasKey_priv,
                        msg_len,
                        msg,
                        (),
                        (),
                        (),
                        (),
                        (),
                    );
                    let ns = super::dpe::session_state::Available(super::dpe::session_state__Available__payload {
                        context: super::dpetypes::context_t::L1_context(c),
                    });
                    let s1 = super::dpe::replace_session(sid, (), ns, ());
                }
                _ => panic!(),
            }
        }
        _ => panic!(),
    }
}
pub fn get_profile(uu___: ()) -> super::dpetypes::profile_descriptor_t {
    super::dpetypes::mk_profile_descriptor(
        "".to_string(),
        1,
        0,
        false,
        false,
        false,
        false,
        0,
        "".to_string(),
        false,
        "".to_string(),
        "".to_string(),
        false,
        true,
        1,
        16,
        false,
        false,
        false,
        false,
        true,
        false,
        false,
        false,
        false,
        false,
        true,
        false,
        false,
        false,
        false,
        false,
        true,
        "".to_string(),
        "".to_string(),
        "".to_string(),
        false,
        "".to_string(),
        "".to_string(),
        "".to_string(),
        false,
        false,
        false,
        "".to_string(),
        "".to_string(),
        "".to_string(),
        false,
        0,
        0,
        false,
        false,
        false,
        false,
        false,
        false,
        false,
        false,
        "".to_string(),
        false,
        "".to_string(),
        "".to_string(),
        "".to_string(),
        false,
        "".to_string(),
        "".to_string(),
        false,
        false,
        false,
        "".to_string(),
    )
}

