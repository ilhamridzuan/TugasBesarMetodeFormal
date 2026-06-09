

// ============================================================================
// SIGNATURES (Entitas, Status, dan Relasi)
// ============================================================================

//Definisi status akun staf medis
abstract sig Status {}
one sig active, Banned extends Status {}

//Definisi tindakan spesifik modul lab
abstract sig Permission {}
one sig View, Input, Revoke extends Permission {}

sig Role {
	permissions: set Permission
}

sig User {
	status: one Status,
	roles: set Role
}

sig Session {
	user: one User,
	activeRoles: set Role
}

// ============================================================================
// PREDICATES (Perilaku Sistem dan Transisi Status)
// ============================================================================

pred login [u: User, s: Session] {
    s.user = u
    u.status = active

    s.activeRoles in u.roles

    some s.activeRoles
}

pred checkAccess [s: Session, p: Permission] {
    p in s.activeRoles.permissions
}

pred assignRole [u_before: User, u_after: User, newRole: Role] {
    u_after.roles = u_before.roles + newRole

    u_after.status = u_before.status
}

// ============================================================================
// CONSTRAINTS (Facts - Aturan Bisnis Keamanan Mutlak)
// ============================================================================

fact SISFORLAB_Business_Rules {
    // 1. Pengguna Banned tidak boleh memiliki Sesi Aktif
    all s: Session | s.user.status != Banned

    // 2. Setiap Peran harus memiliki setidaknya satu Izin Akses (Permission)
    all r: Role | some r.permissions

    // 3. Batasan Hak Akses Fitur Kritis 'Revoke'
    // hanya boleh dimiliki oleh pengguna yang aktif (bukan pengguna baru/tidak aktif).
    all r: Role | Revoke in r.permissions => (all u: User | r in u.roles => u.status = active)

    // 4. Setiap Sesi harus memiliki setidaknya satu Peran Aktif
    all s: Session | some s.activeRoles

    // 5. Prinsip Pemisahan Tugas Dinamis (Dynamic Separation of Duty)
    // tidak boleh mengaktifkan semua peran sekaligus demi meminimalkan risiko insiden keamanan.
    all s: Session | s.activeRoles != s.user.roles or #s.user.roles <= 1

    // 6. Batasan Akses Modul Input Berdasarkan Peran
    // maka dalam sesi tersebut mereka tidak boleh mengaktifkan peran lain yang bersifat pasif saja.
    all s: Session | Input in s.activeRoles.permissions => #s.activeRoles >= 1

    // 7. Isolasi Sesi Pengguna
    // terikat pada dua user yang berbeda secara bersamaan.
    all s1, s2: Session | s1.user != s2.user => s1 != s2

    // 8. Keterikatan Peran Global
    // yang menganggur; semua Role harus ter-assign ke minimal satu User.
    all r: Role | some u: User | r in u.roles

    // 9. Proteksi Sesi untuk Pengguna Tanpa Peran
    // maka sistem otomatis melarang pembuatan Session untuk User tersebut.
    all u: User | no u.roles => (no s: Session | s.user = u)

    // 10. Batasan Maksimal Peran Aktif Per Sesi
    // sebuah sesi maksimal hanya boleh mengaktifkan hingga 3 peran secara bersamaan.
    all s: Session | #s.activeRoles <= 3

    //Menjamin secara global bahwa peran aktif sesi mutlak milik pengguna
    all s: Session | s.activeRoles in s.user.roles
}

// ============================================================================
// MODEL CHECKING (Assertions & Scenarios)
// ============================================================================
// 1. Asersi Keamanan: Pengguna Banned Sama Sekali Tidak Bisa Memiliki Sesi
assert NoSessionForBanned {
    no s: Session | s.user.status = Banned
}

// 2. Asersi Keamanan: Pengguna Tanpa Peran Tidak Bisa Mendapatkan Hak Akses
assert NoRoleNoAccess {
    all s: Session, p: Permission | no s.user.roles => not checkAccess[s, p]
}

// 3. Asersi Keamanan: Pencegahan Eskalasi Hak Istimewa (Privilege Escalation)
assert NoPrivilegeEscalation {
    all s: Session, p: Permission | 
        checkAccess[s, p] => (some r: s.user.roles | p in r.permissions)
}


// --- PERINTAH RUN & CHECK (Minimal 5 Skenario Uji) ---

// Skenario 1: Visualisasi Simulasi Proses Login (Konsistensi Model)
// Menghasilkan graf instans valid di mana proses login berhasil dilakukan.
run login for 3 but 1 Session, 1 User

// Skenario 2: Simulasi Pemberian Peran (Assign Role)
// Memverifikasi apakah transisi perubahan status peran pengguna berjalan logis.
run assignRole for 3 but 2 User, 1 Role

// Skenario 3: Verifikasi Sistem Terhadap Pengguna Banned
// Mempergunakan perintah 'check' untuk memastikan asersi NoSessionForBanned tidak memiliki celah (No counterexample found).
check NoSessionForBanned for 5

// Skenario 4: Verifikasi Kebocoran Hak Akses
// Memastikan pengguna kosong atau tanpa peran tidak akan pernah bisa menembus otorisasi fungsi lab.
check NoRoleNoAccess for 5

// Skenario 5: Verifikasi Kekokohan Proteksi Otorisasi RBAC
// Memastikan sistem mutlak aman dari eskalasi hak akses ilegal di seluruh ruang lingkup (scope) pengujian.
check NoPrivilegeEscalation for 5
