/* automatically generated by rust-bindgen 0.70.1 */

#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct FStar_Bytes_bytes {
    pub length: u32,
    pub data: *const ::std::os::raw::c_char,
}
#[allow(clippy::unnecessary_operation, clippy::identity_op)]
const _: () = {
    ["Size of FStar_Bytes_bytes"][::std::mem::size_of::<FStar_Bytes_bytes>() - 16usize];
    ["Alignment of FStar_Bytes_bytes"][::std::mem::align_of::<FStar_Bytes_bytes>() - 8usize];
    ["Offset of field: FStar_Bytes_bytes::length"]
        [::std::mem::offset_of!(FStar_Bytes_bytes, length) - 0usize];
    ["Offset of field: FStar_Bytes_bytes::data"]
        [::std::mem::offset_of!(FStar_Bytes_bytes, data) - 8usize];
};
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct character_string_t_s {
    pub fst: u32,
    pub snd: FStar_Bytes_bytes,
}
#[allow(clippy::unnecessary_operation, clippy::identity_op)]
const _: () = {
    ["Size of character_string_t_s"][::std::mem::size_of::<character_string_t_s>() - 24usize];
    ["Alignment of character_string_t_s"][::std::mem::align_of::<character_string_t_s>() - 8usize];
    ["Offset of field: character_string_t_s::fst"]
        [::std::mem::offset_of!(character_string_t_s, fst) - 0usize];
    ["Offset of field: character_string_t_s::snd"]
        [::std::mem::offset_of!(character_string_t_s, snd) - 8usize];
};
pub type character_string_t = character_string_t_s;
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct octet_string_t_s {
    pub len: u32,
    pub s: FStar_Bytes_bytes,
}
#[allow(clippy::unnecessary_operation, clippy::identity_op)]
const _: () = {
    ["Size of octet_string_t_s"][::std::mem::size_of::<octet_string_t_s>() - 24usize];
    ["Alignment of octet_string_t_s"][::std::mem::align_of::<octet_string_t_s>() - 8usize];
    ["Offset of field: octet_string_t_s::len"]
        [::std::mem::offset_of!(octet_string_t_s, len) - 0usize];
    ["Offset of field: octet_string_t_s::s"][::std::mem::offset_of!(octet_string_t_s, s) - 8usize];
};
pub type octet_string_t = octet_string_t_s;
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct deviceIDCSR_ingredients_t_s {
    pub ku: i32,
    pub version: i32,
    pub s_common: character_string_t,
    pub s_org: character_string_t,
    pub s_country: character_string_t,
}
#[allow(clippy::unnecessary_operation, clippy::identity_op)]
const _: () = {
    ["Size of deviceIDCSR_ingredients_t_s"]
        [::std::mem::size_of::<deviceIDCSR_ingredients_t_s>() - 80usize];
    ["Alignment of deviceIDCSR_ingredients_t_s"]
        [::std::mem::align_of::<deviceIDCSR_ingredients_t_s>() - 8usize];
    ["Offset of field: deviceIDCSR_ingredients_t_s::ku"]
        [::std::mem::offset_of!(deviceIDCSR_ingredients_t_s, ku) - 0usize];
    ["Offset of field: deviceIDCSR_ingredients_t_s::version"]
        [::std::mem::offset_of!(deviceIDCSR_ingredients_t_s, version) - 4usize];
    ["Offset of field: deviceIDCSR_ingredients_t_s::s_common"]
        [::std::mem::offset_of!(deviceIDCSR_ingredients_t_s, s_common) - 8usize];
    ["Offset of field: deviceIDCSR_ingredients_t_s::s_org"]
        [::std::mem::offset_of!(deviceIDCSR_ingredients_t_s, s_org) - 32usize];
    ["Offset of field: deviceIDCSR_ingredients_t_s::s_country"]
        [::std::mem::offset_of!(deviceIDCSR_ingredients_t_s, s_country) - 56usize];
};
pub type deviceIDCSR_ingredients_t = deviceIDCSR_ingredients_t_s;
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct aliasKeyCRT_ingredients_t_s {
    pub version1: i32,
    pub serialNumber: octet_string_t,
    pub i_common: character_string_t,
    pub i_org: character_string_t,
    pub i_country: character_string_t,
    pub notBefore: FStar_Bytes_bytes,
    pub notAfter: FStar_Bytes_bytes,
    pub s_common1: character_string_t,
    pub s_org1: character_string_t,
    pub s_country1: character_string_t,
    pub ku1: i32,
    pub l0_version: i32,
}
#[allow(clippy::unnecessary_operation, clippy::identity_op)]
const _: () = {
    ["Size of aliasKeyCRT_ingredients_t_s"]
        [::std::mem::size_of::<aliasKeyCRT_ingredients_t_s>() - 216usize];
    ["Alignment of aliasKeyCRT_ingredients_t_s"]
        [::std::mem::align_of::<aliasKeyCRT_ingredients_t_s>() - 8usize];
    ["Offset of field: aliasKeyCRT_ingredients_t_s::version1"]
        [::std::mem::offset_of!(aliasKeyCRT_ingredients_t_s, version1) - 0usize];
    ["Offset of field: aliasKeyCRT_ingredients_t_s::serialNumber"]
        [::std::mem::offset_of!(aliasKeyCRT_ingredients_t_s, serialNumber) - 8usize];
    ["Offset of field: aliasKeyCRT_ingredients_t_s::i_common"]
        [::std::mem::offset_of!(aliasKeyCRT_ingredients_t_s, i_common) - 32usize];
    ["Offset of field: aliasKeyCRT_ingredients_t_s::i_org"]
        [::std::mem::offset_of!(aliasKeyCRT_ingredients_t_s, i_org) - 56usize];
    ["Offset of field: aliasKeyCRT_ingredients_t_s::i_country"]
        [::std::mem::offset_of!(aliasKeyCRT_ingredients_t_s, i_country) - 80usize];
    ["Offset of field: aliasKeyCRT_ingredients_t_s::notBefore"]
        [::std::mem::offset_of!(aliasKeyCRT_ingredients_t_s, notBefore) - 104usize];
    ["Offset of field: aliasKeyCRT_ingredients_t_s::notAfter"]
        [::std::mem::offset_of!(aliasKeyCRT_ingredients_t_s, notAfter) - 120usize];
    ["Offset of field: aliasKeyCRT_ingredients_t_s::s_common1"]
        [::std::mem::offset_of!(aliasKeyCRT_ingredients_t_s, s_common1) - 136usize];
    ["Offset of field: aliasKeyCRT_ingredients_t_s::s_org1"]
        [::std::mem::offset_of!(aliasKeyCRT_ingredients_t_s, s_org1) - 160usize];
    ["Offset of field: aliasKeyCRT_ingredients_t_s::s_country1"]
        [::std::mem::offset_of!(aliasKeyCRT_ingredients_t_s, s_country1) - 184usize];
    ["Offset of field: aliasKeyCRT_ingredients_t_s::ku1"]
        [::std::mem::offset_of!(aliasKeyCRT_ingredients_t_s, ku1) - 208usize];
    ["Offset of field: aliasKeyCRT_ingredients_t_s::l0_version"]
        [::std::mem::offset_of!(aliasKeyCRT_ingredients_t_s, l0_version) - 212usize];
};
pub type aliasKeyCRT_ingredients_t = aliasKeyCRT_ingredients_t_s;
pub struct l0 {
    __library: ::libloading::Library,
    pub len_of_deviceIDCRI: unsafe extern "C" fn(
        version: i32,
        s_common: character_string_t,
        s_org: character_string_t,
        s_country: character_string_t,
    ) -> u32,
    pub len_of_deviceIDCSR: unsafe extern "C" fn(cri_len: u32) -> u32,
    pub len_of_aliasKeyTBS: unsafe extern "C" fn(
        serialNumber: octet_string_t,
        i_common: character_string_t,
        i_org: character_string_t,
        i_country: character_string_t,
        s_common: character_string_t,
        s_org: character_string_t,
        s_country: character_string_t,
        l0_version: i32,
    ) -> u32,
    pub len_of_aliasKeyCRT: unsafe extern "C" fn(tbs_len: u32) -> u32,
    pub l0_get_deviceIDCSR_ingredients: unsafe extern "C" fn() -> deviceIDCSR_ingredients_t,
    pub l0_get_aliasKeyCRT_ingredients: unsafe extern "C" fn() -> aliasKeyCRT_ingredients_t,
    pub l0: unsafe extern "C" fn(
        cdi: *mut u8,
        fwid: *mut u8,
        deviceID_label_len: u32,
        deviceID_label: *mut u8,
        aliasKey_label_len: u32,
        aliasKey_label: *mut u8,
        deviceIDCSR_ingredients: deviceIDCSR_ingredients_t,
        aliasKeyCRT_ingredients: aliasKeyCRT_ingredients_t,
        deviceID_pub: *mut u8,
        aliasKey_pub: *mut u8,
        aliasKey_priv: *mut u8,
        deviceIDCSR_len: u32,
        deviceIDCSR_buf: *mut u8,
        aliasKeyCRT_len: u32,
        aliasKeyCRT_buf: *mut u8,
    ),
}
impl l0 {
    pub unsafe fn new<P>(path: P) -> Result<Self, ::libloading::Error>
    where
        P: AsRef<::std::ffi::OsStr>,
    {
        let library = ::libloading::Library::new(path)?;
        Self::from_library(library)
    }
    pub unsafe fn from_library<L>(library: L) -> Result<Self, ::libloading::Error>
    where
        L: Into<::libloading::Library>,
    {
        let __library = library.into();
        let len_of_deviceIDCRI = __library.get(b"len_of_deviceIDCRI\0").map(|sym| *sym)?;
        let len_of_deviceIDCSR = __library.get(b"len_of_deviceIDCSR\0").map(|sym| *sym)?;
        let len_of_aliasKeyTBS = __library.get(b"len_of_aliasKeyTBS\0").map(|sym| *sym)?;
        let len_of_aliasKeyCRT = __library.get(b"len_of_aliasKeyCRT\0").map(|sym| *sym)?;
        let l0_get_deviceIDCSR_ingredients = __library
            .get(b"l0_get_deviceIDCSR_ingredients\0")
            .map(|sym| *sym)?;
        let l0_get_aliasKeyCRT_ingredients = __library
            .get(b"l0_get_aliasKeyCRT_ingredients\0")
            .map(|sym| *sym)?;
        let l0 = __library.get(b"l0\0").map(|sym| *sym)?;
        Ok(l0 {
            __library,
            len_of_deviceIDCRI,
            len_of_deviceIDCSR,
            len_of_aliasKeyTBS,
            len_of_aliasKeyCRT,
            l0_get_deviceIDCSR_ingredients,
            l0_get_aliasKeyCRT_ingredients,
            l0,
        })
    }
    pub unsafe fn len_of_deviceIDCRI(
        &self,
        version: i32,
        s_common: character_string_t,
        s_org: character_string_t,
        s_country: character_string_t,
    ) -> u32 {
        (self.len_of_deviceIDCRI)(version, s_common, s_org, s_country)
    }
    pub unsafe fn len_of_deviceIDCSR(&self, cri_len: u32) -> u32 {
        (self.len_of_deviceIDCSR)(cri_len)
    }
    pub unsafe fn len_of_aliasKeyTBS(
        &self,
        serialNumber: octet_string_t,
        i_common: character_string_t,
        i_org: character_string_t,
        i_country: character_string_t,
        s_common: character_string_t,
        s_org: character_string_t,
        s_country: character_string_t,
        l0_version: i32,
    ) -> u32 {
        (self.len_of_aliasKeyTBS)(
            serialNumber,
            i_common,
            i_org,
            i_country,
            s_common,
            s_org,
            s_country,
            l0_version,
        )
    }
    pub unsafe fn len_of_aliasKeyCRT(&self, tbs_len: u32) -> u32 {
        (self.len_of_aliasKeyCRT)(tbs_len)
    }
    pub unsafe fn l0_get_deviceIDCSR_ingredients(&self) -> deviceIDCSR_ingredients_t {
        (self.l0_get_deviceIDCSR_ingredients)()
    }
    pub unsafe fn l0_get_aliasKeyCRT_ingredients(&self) -> aliasKeyCRT_ingredients_t {
        (self.l0_get_aliasKeyCRT_ingredients)()
    }
    pub unsafe fn l0(
        &self,
        cdi: *mut u8,
        fwid: *mut u8,
        deviceID_label_len: u32,
        deviceID_label: *mut u8,
        aliasKey_label_len: u32,
        aliasKey_label: *mut u8,
        deviceIDCSR_ingredients: deviceIDCSR_ingredients_t,
        aliasKeyCRT_ingredients: aliasKeyCRT_ingredients_t,
        deviceID_pub: *mut u8,
        aliasKey_pub: *mut u8,
        aliasKey_priv: *mut u8,
        deviceIDCSR_len: u32,
        deviceIDCSR_buf: *mut u8,
        aliasKeyCRT_len: u32,
        aliasKeyCRT_buf: *mut u8,
    ) {
        (self.l0)(
            cdi,
            fwid,
            deviceID_label_len,
            deviceID_label,
            aliasKey_label_len,
            aliasKey_label,
            deviceIDCSR_ingredients,
            aliasKeyCRT_ingredients,
            deviceID_pub,
            aliasKey_pub,
            aliasKey_priv,
            deviceIDCSR_len,
            deviceIDCSR_buf,
            aliasKeyCRT_len,
            aliasKeyCRT_buf,
        )
    }
}
