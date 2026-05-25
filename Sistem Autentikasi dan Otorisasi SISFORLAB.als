

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
