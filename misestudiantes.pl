:- add_lib('setloglibpf.slog').

%%% slits(S): true if S is a set representing a list. This means
%%% that S is a partial function whose domain is equal to [1,n]
%%% for some natural n
slist(S) :- 
  pfun(S) & 
  dom(S,D) &
  size(D,N) &
  subset(D,int(1,N)).

%%% slast(S,L): true if L is the last element of list S
slast(S,L) :- 
  pfun(S) & 
  dom(S,D) &
  size(D,N) &
  subset(D,int(1,N)) &
  [N,L] in S.

%%% sadd(S,E,T): true if T is the list obtained by appending E to the list S
sadd(S,E,T) :- 
  pfun(S) & 
  dom(S,D) &
  size(D,N) &
  subset(D,int(1,N)) &
  M is N + 1 &
  T = {[M,E] / S}.

def_type(grado, int).
def_type(estado, enum([inscripto, promueve, repite])).
def_type(rep, enum([alumnoEsRepitente, alumnoNoEsRepitente, alumnoNoEncontrado])).
def_type(legajos, pfun(alumno, slist(rel(grado, estado)))).
def_type(graduados, set(alumno)).

variables([Legajos, Graduados]).

invariant(graduadoTieneLegajoInv).
graduadoTieneLegajoInv(Legajos, Graduados) :- 
    dom(Legajos, D) & 
    subset(Graduados, D).

:- dec_p_type(legajos, graduados).
initial(misEstudiantesInicial).
misEstudiantesInicial(Legajos, Graduados) :-
    Legajos = {} &
    Graduados = {}.

:- dec_p_type(inscribirAlumnoNuevoOk(legajos, graduados, alumno, legajos, graduados)).
inscribirAlumnoNuevoOk(Legajos, Graduados, Alumno, Legajos_, Graduados_) :-
    nin_dom(Alumno, Legajos) &
    sadd({}, [1, inscripto], I) &
    un(Legajos, {[Alumno, I]} , Legajos_) &
    Graduados_ = Graduados.

:- dec_p_type(inscribirAlumnoPromovidoOk(legajos, graduados, alumno, legajos, graduados)).
inscribirAlumnoPromovidoOk(Legajos, Graduados, Alumnos, Legajos_, Graduados_) :-
    in_dom(Alumno, Legajos) &
    applyTo(Legajos, Alumno, L) &
    slast(L, I) &
    fst(I, G) &
    snd(I, E) &
    E = promueve &
    G < 12 &
    G_ is G + 1 &
    I_ = [G_, inscripto] &
    sadd(L, I_, L_) &
    foplus(Legajos, Alumno, L_, Legajos_) &
    Graduados_ = Graduados.

:- dec_p_type(inscribirAlumnoRepitenteOk(legajos, graduados, alumno, legajos, graduados)).
inscribirAlumnoRepitenteOk(Legajos, Graduados, Alumnos, Legajos_, Graduados_) :-
    in_dom(Alumno, Legajos) &
    applyTo(Legajos, Alumno, L) &
    slast(L, I) &
    fst(I, G) &
    snd(I, E) &
    E = repite &
    G < 13 &
    I_ = [G, inscripto] &
    sadd(L, I_, L_) &
    foplus(Legajos, Alumno, L_, Legajos_) &
    Graduados_ = Graduados.

:- dec_p_type(inscribirAlumnoGraduadoE(legajos, graduados, alumno, legajos, graduados)).
inscribirAlumnoGraduadoE(Legajos, Graduados, Alumnos, Legajos_, Graduados_) :-
    in_dom(Alumno, Legajos) &
    applyTo(Legajos, Alumno, L) &
    slast(L, I) &
    fst(I, G) &
    snd(I, E) &
    E = promueve &
    G = 12 &
    Legajos_ = Legajos  &
    Graduados_ = Graduados.

:- dec_p_type(inscribirAlumnoDobleInscripE(legajos, graduados, alumno, legajos, graduados)).
inscribirAlumnoDobleInscripE(Legajos, Graduados, Alumnos, Legajos_, Graduados_) :-
    in_dom(Alumno, Legajos) &
    applyTo(Legajos, Alumno, L) &
    slast(L, I) &
    snd(I, E) &
    E = inscripto &
    Legajos_ = Legajos  &
    Graduados_ = Graduados.

operation(inscribirAlumno).
dec_p_type(inscribirAlumno(legajos, graduados, alumno, legajos, graduados)).
inscribirAlumno(Legajo, Graduados, Alumno_i, Legajos_, Graduados_) :-
    inscribirAlumnoNuevoOk(Legajos, Graduados, Alumno_i, Legajos_, Graduados) or
    inscribirAlumnoPromovidoOk(Legajos, Graduados, Alumno_i, Legajos_, Graduados) or
    inscribirAlumnoRepetidoOk(Legajos, Graduados, Alumno_i, Legajos_, Graduados) or
    inscribirAlumnoGraduadoE(Legajos, Graduados, Alumno_i, Legajos_, Graduados) or
    inscribirAlumnoDobleInscripE(Legajos, Graduados, Alumno_i, Legajos_, Graduados).
