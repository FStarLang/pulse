/* automatically generated by rust-bindgen 0.69.1 */

pub const CBOR_Case_Int64: u32 = 0;
pub const CBOR_Case_String: u32 = 1;
pub const CBOR_Case_Tagged: u32 = 2;
pub const CBOR_Case_Array: u32 = 3;
pub const CBOR_Case_Map: u32 = 4;
pub const CBOR_Case_Simple_value: u32 = 5;
pub const CBOR_Case_Serialized: u32 = 6;
pub const CBOR_MAJOR_TYPE_SIMPLE_VALUE: u32 = 7;
pub const CBOR_MAJOR_TYPE_UINT64: u32 = 0;
pub const CBOR_MAJOR_TYPE_NEG_INT64: u32 = 1;
pub const CBOR_MAJOR_TYPE_BYTE_STRING: u32 = 2;
pub const CBOR_MAJOR_TYPE_TEXT_STRING: u32 = 3;
pub const CBOR_MAJOR_TYPE_ARRAY: u32 = 4;
pub const CBOR_MAJOR_TYPE_MAP: u32 = 5;
pub const CBOR_MAJOR_TYPE_TAGGED: u32 = 6;
pub const CBOR_Array_Iterator_Payload_Array: u32 = 0;
pub const CBOR_Array_Iterator_Payload_Serialized: u32 = 1;
pub const CBOR_Map_Iterator_Payload_Map: u32 = 0;
pub const CBOR_Map_Iterator_Payload_Serialized: u32 = 1;
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct cbor_int_s {
    pub cbor_int_type: u8,
    pub cbor_int_value: u64,
}
#[test]
fn bindgen_test_layout_cbor_int_s() {
    const UNINIT: ::std::mem::MaybeUninit<cbor_int_s> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<cbor_int_s>(),
        16usize,
        concat!("Size of: ", stringify!(cbor_int_s))
    );
    assert_eq!(
        ::std::mem::align_of::<cbor_int_s>(),
        8usize,
        concat!("Alignment of ", stringify!(cbor_int_s))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).cbor_int_type) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_int_s),
            "::",
            stringify!(cbor_int_type)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).cbor_int_value) as usize - ptr as usize },
        8usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_int_s),
            "::",
            stringify!(cbor_int_value)
        )
    );
}
pub type cbor_int = cbor_int_s;
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct cbor_string_s {
    pub cbor_string_type: u8,
    pub cbor_string_length: u64,
    pub cbor_string_payload: *mut u8,
}
#[test]
fn bindgen_test_layout_cbor_string_s() {
    const UNINIT: ::std::mem::MaybeUninit<cbor_string_s> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<cbor_string_s>(),
        24usize,
        concat!("Size of: ", stringify!(cbor_string_s))
    );
    assert_eq!(
        ::std::mem::align_of::<cbor_string_s>(),
        8usize,
        concat!("Alignment of ", stringify!(cbor_string_s))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).cbor_string_type) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_string_s),
            "::",
            stringify!(cbor_string_type)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).cbor_string_length) as usize - ptr as usize },
        8usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_string_s),
            "::",
            stringify!(cbor_string_length)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).cbor_string_payload) as usize - ptr as usize },
        16usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_string_s),
            "::",
            stringify!(cbor_string_payload)
        )
    );
}
pub type cbor_string = cbor_string_s;
pub type cbor = cbor_s;
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct cbor_tagged0_s {
    pub cbor_tagged0_tag: u64,
    pub cbor_tagged0_payload: *mut cbor,
}
#[test]
fn bindgen_test_layout_cbor_tagged0_s() {
    const UNINIT: ::std::mem::MaybeUninit<cbor_tagged0_s> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<cbor_tagged0_s>(),
        16usize,
        concat!("Size of: ", stringify!(cbor_tagged0_s))
    );
    assert_eq!(
        ::std::mem::align_of::<cbor_tagged0_s>(),
        8usize,
        concat!("Alignment of ", stringify!(cbor_tagged0_s))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).cbor_tagged0_tag) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_tagged0_s),
            "::",
            stringify!(cbor_tagged0_tag)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).cbor_tagged0_payload) as usize - ptr as usize },
        8usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_tagged0_s),
            "::",
            stringify!(cbor_tagged0_payload)
        )
    );
}
pub type cbor_tagged0 = cbor_tagged0_s;
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct cbor_array_s {
    pub cbor_array_length: u64,
    pub cbor_array_payload: *mut cbor,
}
#[test]
fn bindgen_test_layout_cbor_array_s() {
    const UNINIT: ::std::mem::MaybeUninit<cbor_array_s> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<cbor_array_s>(),
        16usize,
        concat!("Size of: ", stringify!(cbor_array_s))
    );
    assert_eq!(
        ::std::mem::align_of::<cbor_array_s>(),
        8usize,
        concat!("Alignment of ", stringify!(cbor_array_s))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).cbor_array_length) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_array_s),
            "::",
            stringify!(cbor_array_length)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).cbor_array_payload) as usize - ptr as usize },
        8usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_array_s),
            "::",
            stringify!(cbor_array_payload)
        )
    );
}
pub type cbor_array = cbor_array_s;
pub type cbor_map_entry = cbor_map_entry_s;
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct cbor_map_s {
    pub cbor_map_length: u64,
    pub cbor_map_payload: *mut cbor_map_entry,
}
#[test]
fn bindgen_test_layout_cbor_map_s() {
    const UNINIT: ::std::mem::MaybeUninit<cbor_map_s> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<cbor_map_s>(),
        16usize,
        concat!("Size of: ", stringify!(cbor_map_s))
    );
    assert_eq!(
        ::std::mem::align_of::<cbor_map_s>(),
        8usize,
        concat!("Alignment of ", stringify!(cbor_map_s))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).cbor_map_length) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_map_s),
            "::",
            stringify!(cbor_map_length)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).cbor_map_payload) as usize - ptr as usize },
        8usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_map_s),
            "::",
            stringify!(cbor_map_payload)
        )
    );
}
pub type cbor_map = cbor_map_s;
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct cbor_serialized_s {
    pub cbor_serialized_size: usize,
    pub cbor_serialized_payload: *mut u8,
}
#[test]
fn bindgen_test_layout_cbor_serialized_s() {
    const UNINIT: ::std::mem::MaybeUninit<cbor_serialized_s> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<cbor_serialized_s>(),
        16usize,
        concat!("Size of: ", stringify!(cbor_serialized_s))
    );
    assert_eq!(
        ::std::mem::align_of::<cbor_serialized_s>(),
        8usize,
        concat!("Alignment of ", stringify!(cbor_serialized_s))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).cbor_serialized_size) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_serialized_s),
            "::",
            stringify!(cbor_serialized_size)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).cbor_serialized_payload) as usize - ptr as usize },
        8usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_serialized_s),
            "::",
            stringify!(cbor_serialized_payload)
        )
    );
}
pub type cbor_serialized = cbor_serialized_s;
pub type cbor_tags = u8;
#[repr(C)]
#[derive(Copy, Clone)]
pub struct cbor_s {
    pub tag: cbor_tags,
    pub __bindgen_anon_1: cbor_s__bindgen_ty_1,
}
#[repr(C)]
#[derive(Copy, Clone)]
pub union cbor_s__bindgen_ty_1 {
    pub case_CBOR_Case_Int64: cbor_int,
    pub case_CBOR_Case_String: cbor_string,
    pub case_CBOR_Case_Tagged: cbor_tagged0,
    pub case_CBOR_Case_Array: cbor_array,
    pub case_CBOR_Case_Map: cbor_map,
    pub case_CBOR_Case_Simple_value: u8,
    pub case_CBOR_Case_Serialized: cbor_serialized,
}
#[test]
fn bindgen_test_layout_cbor_s__bindgen_ty_1() {
    const UNINIT: ::std::mem::MaybeUninit<cbor_s__bindgen_ty_1> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<cbor_s__bindgen_ty_1>(),
        24usize,
        concat!("Size of: ", stringify!(cbor_s__bindgen_ty_1))
    );
    assert_eq!(
        ::std::mem::align_of::<cbor_s__bindgen_ty_1>(),
        8usize,
        concat!("Alignment of ", stringify!(cbor_s__bindgen_ty_1))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).case_CBOR_Case_Int64) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_s__bindgen_ty_1),
            "::",
            stringify!(case_CBOR_Case_Int64)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).case_CBOR_Case_String) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_s__bindgen_ty_1),
            "::",
            stringify!(case_CBOR_Case_String)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).case_CBOR_Case_Tagged) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_s__bindgen_ty_1),
            "::",
            stringify!(case_CBOR_Case_Tagged)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).case_CBOR_Case_Array) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_s__bindgen_ty_1),
            "::",
            stringify!(case_CBOR_Case_Array)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).case_CBOR_Case_Map) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_s__bindgen_ty_1),
            "::",
            stringify!(case_CBOR_Case_Map)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).case_CBOR_Case_Simple_value) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_s__bindgen_ty_1),
            "::",
            stringify!(case_CBOR_Case_Simple_value)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).case_CBOR_Case_Serialized) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_s__bindgen_ty_1),
            "::",
            stringify!(case_CBOR_Case_Serialized)
        )
    );
}
#[test]
fn bindgen_test_layout_cbor_s() {
    const UNINIT: ::std::mem::MaybeUninit<cbor_s> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<cbor_s>(),
        32usize,
        concat!("Size of: ", stringify!(cbor_s))
    );
    assert_eq!(
        ::std::mem::align_of::<cbor_s>(),
        8usize,
        concat!("Alignment of ", stringify!(cbor_s))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).tag) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_s),
            "::",
            stringify!(tag)
        )
    );
}
extern "C" {
    pub fn cbor_get_major_type(a: cbor) -> u8;
}
extern "C" {
    pub fn cbor_write(c: cbor, out: *mut u8, sz: usize) -> usize;
}
#[repr(C)]
#[derive(Copy, Clone)]
pub struct cbor_map_entry_s {
    pub cbor_map_entry_key: cbor,
    pub cbor_map_entry_value: cbor,
}
#[test]
fn bindgen_test_layout_cbor_map_entry_s() {
    const UNINIT: ::std::mem::MaybeUninit<cbor_map_entry_s> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<cbor_map_entry_s>(),
        64usize,
        concat!("Size of: ", stringify!(cbor_map_entry_s))
    );
    assert_eq!(
        ::std::mem::align_of::<cbor_map_entry_s>(),
        8usize,
        concat!("Alignment of ", stringify!(cbor_map_entry_s))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).cbor_map_entry_key) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_map_entry_s),
            "::",
            stringify!(cbor_map_entry_key)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).cbor_map_entry_value) as usize - ptr as usize },
        32usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_map_entry_s),
            "::",
            stringify!(cbor_map_entry_value)
        )
    );
}
pub type cbor_array_iterator_payload_t_tags = u8;
#[repr(C)]
#[derive(Copy, Clone)]
pub struct cbor_array_iterator_payload_t_s {
    pub tag: cbor_array_iterator_payload_t_tags,
    pub __bindgen_anon_1: cbor_array_iterator_payload_t_s__bindgen_ty_1,
}
#[repr(C)]
#[derive(Copy, Clone)]
pub union cbor_array_iterator_payload_t_s__bindgen_ty_1 {
    pub case_CBOR_Array_Iterator_Payload_Array: *mut cbor,
    pub case_CBOR_Array_Iterator_Payload_Serialized: *mut u8,
}
#[test]
fn bindgen_test_layout_cbor_array_iterator_payload_t_s__bindgen_ty_1() {
    const UNINIT: ::std::mem::MaybeUninit<cbor_array_iterator_payload_t_s__bindgen_ty_1> =
        ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<cbor_array_iterator_payload_t_s__bindgen_ty_1>(),
        8usize,
        concat!(
            "Size of: ",
            stringify!(cbor_array_iterator_payload_t_s__bindgen_ty_1)
        )
    );
    assert_eq!(
        ::std::mem::align_of::<cbor_array_iterator_payload_t_s__bindgen_ty_1>(),
        8usize,
        concat!(
            "Alignment of ",
            stringify!(cbor_array_iterator_payload_t_s__bindgen_ty_1)
        )
    );
    assert_eq!(
        unsafe {
            ::std::ptr::addr_of!((*ptr).case_CBOR_Array_Iterator_Payload_Array) as usize
                - ptr as usize
        },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_array_iterator_payload_t_s__bindgen_ty_1),
            "::",
            stringify!(case_CBOR_Array_Iterator_Payload_Array)
        )
    );
    assert_eq!(
        unsafe {
            ::std::ptr::addr_of!((*ptr).case_CBOR_Array_Iterator_Payload_Serialized) as usize
                - ptr as usize
        },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_array_iterator_payload_t_s__bindgen_ty_1),
            "::",
            stringify!(case_CBOR_Array_Iterator_Payload_Serialized)
        )
    );
}
#[test]
fn bindgen_test_layout_cbor_array_iterator_payload_t_s() {
    const UNINIT: ::std::mem::MaybeUninit<cbor_array_iterator_payload_t_s> =
        ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<cbor_array_iterator_payload_t_s>(),
        16usize,
        concat!("Size of: ", stringify!(cbor_array_iterator_payload_t_s))
    );
    assert_eq!(
        ::std::mem::align_of::<cbor_array_iterator_payload_t_s>(),
        8usize,
        concat!("Alignment of ", stringify!(cbor_array_iterator_payload_t_s))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).tag) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_array_iterator_payload_t_s),
            "::",
            stringify!(tag)
        )
    );
}
pub type cbor_array_iterator_payload_t = cbor_array_iterator_payload_t_s;
#[repr(C)]
#[derive(Copy, Clone)]
pub struct cbor_array_iterator_t_s {
    pub cbor_array_iterator_length: u64,
    pub cbor_array_iterator_payload: cbor_array_iterator_payload_t,
}
#[test]
fn bindgen_test_layout_cbor_array_iterator_t_s() {
    const UNINIT: ::std::mem::MaybeUninit<cbor_array_iterator_t_s> =
        ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<cbor_array_iterator_t_s>(),
        24usize,
        concat!("Size of: ", stringify!(cbor_array_iterator_t_s))
    );
    assert_eq!(
        ::std::mem::align_of::<cbor_array_iterator_t_s>(),
        8usize,
        concat!("Alignment of ", stringify!(cbor_array_iterator_t_s))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).cbor_array_iterator_length) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_array_iterator_t_s),
            "::",
            stringify!(cbor_array_iterator_length)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).cbor_array_iterator_payload) as usize - ptr as usize },
        8usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_array_iterator_t_s),
            "::",
            stringify!(cbor_array_iterator_payload)
        )
    );
}
pub type cbor_array_iterator_t = cbor_array_iterator_t_s;
pub type cbor_map_iterator_payload_t_tags = u8;
#[repr(C)]
#[derive(Copy, Clone)]
pub struct cbor_map_iterator_payload_t_s {
    pub tag: cbor_map_iterator_payload_t_tags,
    pub __bindgen_anon_1: cbor_map_iterator_payload_t_s__bindgen_ty_1,
}
#[repr(C)]
#[derive(Copy, Clone)]
pub union cbor_map_iterator_payload_t_s__bindgen_ty_1 {
    pub case_CBOR_Map_Iterator_Payload_Map: *mut cbor_map_entry,
    pub case_CBOR_Map_Iterator_Payload_Serialized: *mut u8,
}
#[test]
fn bindgen_test_layout_cbor_map_iterator_payload_t_s__bindgen_ty_1() {
    const UNINIT: ::std::mem::MaybeUninit<cbor_map_iterator_payload_t_s__bindgen_ty_1> =
        ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<cbor_map_iterator_payload_t_s__bindgen_ty_1>(),
        8usize,
        concat!(
            "Size of: ",
            stringify!(cbor_map_iterator_payload_t_s__bindgen_ty_1)
        )
    );
    assert_eq!(
        ::std::mem::align_of::<cbor_map_iterator_payload_t_s__bindgen_ty_1>(),
        8usize,
        concat!(
            "Alignment of ",
            stringify!(cbor_map_iterator_payload_t_s__bindgen_ty_1)
        )
    );
    assert_eq!(
        unsafe {
            ::std::ptr::addr_of!((*ptr).case_CBOR_Map_Iterator_Payload_Map) as usize - ptr as usize
        },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_map_iterator_payload_t_s__bindgen_ty_1),
            "::",
            stringify!(case_CBOR_Map_Iterator_Payload_Map)
        )
    );
    assert_eq!(
        unsafe {
            ::std::ptr::addr_of!((*ptr).case_CBOR_Map_Iterator_Payload_Serialized) as usize
                - ptr as usize
        },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_map_iterator_payload_t_s__bindgen_ty_1),
            "::",
            stringify!(case_CBOR_Map_Iterator_Payload_Serialized)
        )
    );
}
#[test]
fn bindgen_test_layout_cbor_map_iterator_payload_t_s() {
    const UNINIT: ::std::mem::MaybeUninit<cbor_map_iterator_payload_t_s> =
        ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<cbor_map_iterator_payload_t_s>(),
        16usize,
        concat!("Size of: ", stringify!(cbor_map_iterator_payload_t_s))
    );
    assert_eq!(
        ::std::mem::align_of::<cbor_map_iterator_payload_t_s>(),
        8usize,
        concat!("Alignment of ", stringify!(cbor_map_iterator_payload_t_s))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).tag) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_map_iterator_payload_t_s),
            "::",
            stringify!(tag)
        )
    );
}
pub type cbor_map_iterator_payload_t = cbor_map_iterator_payload_t_s;
#[repr(C)]
#[derive(Copy, Clone)]
pub struct cbor_map_iterator_t_s {
    pub cbor_map_iterator_length: u64,
    pub cbor_map_iterator_payload: cbor_map_iterator_payload_t,
}
#[test]
fn bindgen_test_layout_cbor_map_iterator_t_s() {
    const UNINIT: ::std::mem::MaybeUninit<cbor_map_iterator_t_s> =
        ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<cbor_map_iterator_t_s>(),
        24usize,
        concat!("Size of: ", stringify!(cbor_map_iterator_t_s))
    );
    assert_eq!(
        ::std::mem::align_of::<cbor_map_iterator_t_s>(),
        8usize,
        concat!("Alignment of ", stringify!(cbor_map_iterator_t_s))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).cbor_map_iterator_length) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_map_iterator_t_s),
            "::",
            stringify!(cbor_map_iterator_length)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).cbor_map_iterator_payload) as usize - ptr as usize },
        8usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_map_iterator_t_s),
            "::",
            stringify!(cbor_map_iterator_payload)
        )
    );
}
pub type cbor_map_iterator_t = cbor_map_iterator_t_s;
extern "C" {
    pub static mut cbor_dummy: cbor;
}
extern "C" {
    pub fn cbor_map_entry_key(uu___: cbor_map_entry) -> cbor;
}
extern "C" {
    pub fn cbor_map_entry_value(uu___: cbor_map_entry) -> cbor;
}
extern "C" {
    pub fn cbor_mk_map_entry(key: cbor, value: cbor) -> cbor_map_entry;
}
extern "C" {
    pub fn cbor_compare_aux(c1: cbor, c2: cbor) -> i16;
}
extern "C" {
    pub fn cbor_constr_array(a: *mut cbor, len: u64) -> cbor;
}
extern "C" {
    pub fn cbor_array_length(a: cbor) -> u64;
}
extern "C" {
    pub fn cbor_array_index(a: cbor, i: usize) -> cbor;
}
extern "C" {
    pub static mut cbor_dummy_array_iterator: cbor_array_iterator_t;
}
extern "C" {
    pub fn cbor_array_iterator_init(a: cbor) -> cbor_array_iterator_t;
}
extern "C" {
    pub fn cbor_array_iterator_is_done(i: cbor_array_iterator_t) -> bool;
}
extern "C" {
    pub fn cbor_array_iterator_next(pi: *mut cbor_array_iterator_t) -> cbor;
}
extern "C" {
    pub fn cbor_read_array(a: cbor, dest: *mut cbor, len: u64) -> *mut cbor;
}
extern "C" {
    pub fn cbor_destr_string(c: cbor) -> cbor_string;
}
extern "C" {
    pub fn cbor_constr_string(typ: u8, a: *mut u8, len: u64) -> cbor;
}
extern "C" {
    pub fn cbor_destr_simple_value(c: cbor) -> u8;
}
extern "C" {
    pub fn cbor_constr_simple_value(value: u8) -> cbor;
}
extern "C" {
    pub fn cbor_destr_int64(c: cbor) -> cbor_int;
}
extern "C" {
    pub fn cbor_constr_int64(ty: u8, value: u64) -> cbor;
}
#[repr(C)]
#[derive(Copy, Clone)]
pub struct cbor_tagged_s {
    pub cbor_tagged_tag: u64,
    pub cbor_tagged_payload: cbor,
}
#[test]
fn bindgen_test_layout_cbor_tagged_s() {
    const UNINIT: ::std::mem::MaybeUninit<cbor_tagged_s> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<cbor_tagged_s>(),
        40usize,
        concat!("Size of: ", stringify!(cbor_tagged_s))
    );
    assert_eq!(
        ::std::mem::align_of::<cbor_tagged_s>(),
        8usize,
        concat!("Alignment of ", stringify!(cbor_tagged_s))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).cbor_tagged_tag) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_tagged_s),
            "::",
            stringify!(cbor_tagged_tag)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).cbor_tagged_payload) as usize - ptr as usize },
        8usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_tagged_s),
            "::",
            stringify!(cbor_tagged_payload)
        )
    );
}
pub type cbor_tagged = cbor_tagged_s;
extern "C" {
    pub fn cbor_destr_tagged(a: cbor) -> cbor_tagged;
}
extern "C" {
    pub fn cbor_constr_tagged(tag: u64, a: *mut cbor) -> cbor;
}
extern "C" {
    pub fn cbor_map_length(a: cbor) -> u64;
}
extern "C" {
    pub static mut cbor_dummy_map_iterator: cbor_map_iterator_t;
}
extern "C" {
    pub fn cbor_constr_map(a: *mut cbor_map_entry, len: u64) -> cbor;
}
extern "C" {
    pub fn cbor_map_iterator_init(a: cbor) -> cbor_map_iterator_t;
}
extern "C" {
    pub fn cbor_map_iterator_is_done(i: cbor_map_iterator_t) -> bool;
}
extern "C" {
    pub fn cbor_map_iterator_next(pi: *mut cbor_map_iterator_t) -> cbor_map_entry;
}
#[repr(C)]
#[derive(Copy, Clone)]
pub struct cbor_read_t_s {
    pub cbor_read_is_success: bool,
    pub cbor_read_payload: cbor,
    pub cbor_read_remainder: *mut u8,
    pub cbor_read_remainder_length: usize,
}
#[test]
fn bindgen_test_layout_cbor_read_t_s() {
    const UNINIT: ::std::mem::MaybeUninit<cbor_read_t_s> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<cbor_read_t_s>(),
        56usize,
        concat!("Size of: ", stringify!(cbor_read_t_s))
    );
    assert_eq!(
        ::std::mem::align_of::<cbor_read_t_s>(),
        8usize,
        concat!("Alignment of ", stringify!(cbor_read_t_s))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).cbor_read_is_success) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_read_t_s),
            "::",
            stringify!(cbor_read_is_success)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).cbor_read_payload) as usize - ptr as usize },
        8usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_read_t_s),
            "::",
            stringify!(cbor_read_payload)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).cbor_read_remainder) as usize - ptr as usize },
        40usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_read_t_s),
            "::",
            stringify!(cbor_read_remainder)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).cbor_read_remainder_length) as usize - ptr as usize },
        48usize,
        concat!(
            "Offset of field: ",
            stringify!(cbor_read_t_s),
            "::",
            stringify!(cbor_read_remainder_length)
        )
    );
}
pub type cbor_read_t = cbor_read_t_s;
extern "C" {
    pub fn cbor_read(a: *mut u8, sz: usize) -> cbor_read_t;
}
extern "C" {
    pub fn cbor_read_deterministically_encoded(a: *mut u8, sz: usize) -> cbor_read_t;
}