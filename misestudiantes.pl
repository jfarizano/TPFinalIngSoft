def_type(grado, int).
def_type(estado, enum([inscripto, promueve, repite])).
def_type(rep, enum([alumnoEsRepitente, alumnoNoEsRepitente, alumnoNoEncontrado])).
def_type(inscripcion, [grado, estado]).
def_type(legajo, rel(int, inscripcion)).
def_type(legajos, rel(alumno, legajo)).
def_type(alumnos, set(alumno)).

%%% ==========================================================================
%%% Funciones copiadas de las librerías para agregar las declaraciones de 
%%% tipos necesarias para usar el type checker
%%% ==========================================================================

dec_pp_type(inDom(X, rel(X,Y))).
inDom(Item, Rel) :- 
    dom(Rel, {Item/Z}) & dec(Z, set(X)).

dec_pp_type(ninDom(X, rel(X,Y))).
ninDom(Item, Rel) :- 
    dom(Rel, Z) & dec(Z, set(X)) & Item nin Z.

dec_pp_type(slist(rel(int, X))).
slist(S) :-
  pfun(S) &
  dom(S,D) &
  dec(D, set(int)) &
  size(D,N) &
  dec(N, int) &
  subset(D,int(1,N)).

%%% slast(S,L): true if L is the last element of list S
dec_pp_type(slast(rel(int, X), X)).
slast(S,L) :- 
  pfun(S) & 
  dom(S,D) &
  dec(D, set(int)) &
  size(D,N) &
  dec(N, int) &
  subset(D,int(1,N)) &
  [N,L] in S.

%%% sadd(S,E,T): true if T is the list obtained by appending E to the list S
dec_pp_type(sadd(rel(int, X), X, rel(int, X))).
sadd(S,E,T) :- 
  pfun(S) & 
  dom(S,D) &
  dec(D, set(int)) &
  size(D,N) &
  dec(N, int) &
  subset(D,int(1,N)) &
  M is N + 1 &
  dec(M, int) &
  T = {[M,E] / S}.

%%% ==========================================================================
%%% ==========================================================================

variables([Legajos, Graduados]).

invariant(graduadoTieneLegajoInv).
dec_p_type(graduadoTieneLegajoInv(legajos, alumnos)).
graduadoTieneLegajoInv(Legajos, Graduados) :-
    let([D],
        dom(Legajos, D) & dec(D, alumnos),
        subset(Graduados, D)
    ).

dec_p_type(n_graduadoTieneLegajoInv(legajos, alumnos)).
n_graduadoTieneLegajoInv(Legajos, Graduados) :-
    neg(let([D],
            dom(Legajos, D) & dec(D, alumnos),
            subset(Graduados, D)
    )).

invariant(legajosPfunInv).
dec_p_type(legajosPfunInv(legajos)).
legajosPfunInv(Legajos) :-
    pfun(Legajos).

dec_p_type(n_legajosPfunInv(legajos)).
n_legajosPfunInv(Legajos) :-
    npfun(Legajos).

dec_p_type(misEstudiantesInicial(legajos, alumnos)).
initial(misEstudiantesInicial).
misEstudiantesInicial(Legajos, Graduados) :-
    Legajos = {} &
    Graduados = {}.

dec_p_type(inscribirAlumnoOk(legajos, alumnos, alumno, legajos, alumnos)).
inscribirAlumnoOk(Legajos, Graduados, Alumno, Legajos_, Graduados_) :-
    ninDom(Alumno, Legajos) &
    sadd({}, [1, inscripto], L) &
    dec(L, legajo) &
    un(Legajos, {[Alumno, L]} , Legajos_) &
    Graduados_ = Graduados.

dec_p_type(inscribirAlumnoRegistradoE(legajos, alumnos, alumno, legajos, alumnos)).
inscribirAlumnoRegistradoE(Legajos, Graduados, Alumno, Legajos_, Graduados_) :-
    inDom(Alumno, Legajos) &
    Legajos_ = Legajos &
    Graduados_ = Graduados.

operation(inscribirAlumno).
dec_p_type(inscribirAlumno(legajos, alumnos, alumno, legajos, alumnos)).
inscribirAlumno(Legajos, Graduados, Alumno, Legajos_, Graduados_) :-
    inscribirAlumnoOk(Legajos, Graduados, Alumno, Legajos_, Graduados_) or
    inscribirAlumnoRegistradoE(Legajos, Graduados, Alumno, Legajos_, Graduados_).

dec_p_type(reinscribirAlumnoPromovidoOk(legajos, alumnos, alumno, legajos, alumnos)).
reinscribirAlumnoPromovidoOk(Legajos, Graduados, Alumno, Legajos_, Graduados_) :-
    inDom(Alumno, Legajos) &
    applyTo(Legajos, Alumno, L) &
    dec(L, legajo) &
    slast(L, I) &
    dec(I, inscripcion) &
    [G, E] = I &
    dec(G, grado) &
    dec(E, estado) &
    G < 12 &
    E = promueve &
    G_ is G + 1 &
    dec(G_, grado) &
    I_ = [G_, inscripto] &
    dec(I_, inscripcion) &
    sadd(L, I_, L_) &
    dec(L_, legajo) &
    oplus(Legajos, {[Alumno, L_]}, Legajos_) &
    Graduados_ = Graduados.

dec_p_type(reinscribirAlumnoRepitenteOk(legajos, alumnos, alumno, legajos, alumnos)).
reinscribirAlumnoRepitenteOk(Legajos, Graduados, Alumno, Legajos_, Graduados_) :-
    inDom(Alumno, Legajos) &
    applyTo(Legajos, Alumno, L) &
    dec(L, legajo) &
    slast(L, I) &
    dec(I, inscripcion) &
    [G, E] = I &
    dec(G, grado) &
    dec(E, estado) &
    G =< 12 &
    E = repite &
    I_ = [G, inscripto] &
    dec(I_, inscripcion) &
    sadd(L, I_, L_) &
    dec(L_, legajo) &
    oplus(Legajos, {[Alumno, L_]}, Legajos_) &
    Graduados_ = Graduados.

dec_p_type(reinscribirAlumnoNoEncontradoE(legajos, alumnos, alumno, legajos, alumnos)).
reinscribirAlumnoNoEncontradoE(Legajos, Graduados, Alumno, Legajos_, Graduados_) :-
    ninDom(Alumno, Legajos) &
    Legajos_ = Legajos &
    Graduados_ = Graduados.

dec_p_type(reinscribirAlumnoGraduadoE(legajos, alumnos, alumno, legajos, alumnos)).
reinscribirAlumnoGraduadoE(Legajos, Graduados, Alumno, Legajos_, Graduados_) :-
    inDom(Alumno, Legajos) &
    applyTo(Legajos, Alumno, L) &
    dec(L, legajo) &
    slast(L, I) &
    dec(I, inscripcion) &
    [G, E] = I &
    dec(G, grado) &
    dec(E, estado) &
    G = 12 &
    E = promueve &
    Legajos_ = Legajos  &
    Graduados_ = Graduados.

dec_p_type(reinscribirAlumnoDobleInscripE(legajos, alumnos, alumno, legajos, alumnos)).
reinscribirAlumnoDobleInscripE(Legajos, Graduados, Alumno, Legajos_, Graduados_) :-
    inDom(Alumno, Legajos) &
    applyTo(Legajos, Alumno, L) &
    dec(L, legajo) &
    slast(L, I) &
    dec(I, inscripcion) &
    [G, E] = I &
    dec(G, grado) &
    dec(E, estado) &
    E = inscripto &
    Legajos_ = Legajos  &
    Graduados_ = Graduados.

operation(reinscribirAlumno).
dec_p_type(reinscribirAlumno(legajos, alumnos, alumno, legajos, alumnos)).
reinscribirAlumno(Legajos, Graduados, Alumno, Legajos_, Graduados_) :-
    reinscribirAlumnoPromovidoOk(Legajos, Graduados, Alumno, Legajos_, Graduados_) or
    reinscribirAlumnoRepitenteOk(Legajos, Graduados, Alumno, Legajos_, Graduados_) or
    reinscribirAlumnoNoEncontradoE(Legajos, Graduados, Alumno, Legajos_, Graduados_) or
    reinscribirAlumnoGraduadoE(Legajos, Graduados, Alumno, Legajos_, Graduados_) or
    reinscribirAlumnoDobleInscripE(Legajos, Graduados, Alumno, Legajos_, Graduados_).

dec_p_type(cerrarInscripcionNoGraduadoOk(legajos, alumnos, alumno, estado, legajos, alumnos)).
cerrarInscripcionNoGraduadoOk(Legajos, Graduados, Alumno, Estado, Legajos_, Graduados_) :-
    inDom(Alumno, Legajos) &
    applyTo(Legajos, Alumno, L) &
    dec(L, legajo) &
    slast(L, I) &
    dec(I, inscripcion) &
    [G, E] = I &
    dec(G, grado) &
    dec(E, estado) &
    (Estado = repite or (Estado = promueve & G < 12)) &
    E = inscripto &
    I_ = [G, Estado] &
    dec(I_, inscripcion) &
    sadd(L, I_, L_) &
    dec(L_, legajo) &
    oplus(Legajos, {[Alumno, L_]}, Legajos_) &
    Graduados_ = Graduados.

dec_p_type(cerrarInscripcionGraduadoOk(legajos, alumnos, alumno, estado, legajos, alumnos)).
cerrarInscripcionGraduadoOk(Legajos, Graduados, Alumno, Estado, Legajos_, Graduados_) :-
    inDom(Alumno, Legajos) &
    applyTo(Legajos, Alumno, L) &
    dec(L, legajo) &
    slast(L, I) &
    dec(I, inscripcion) &
    [G, E] = I &
    dec(G, grado) &
    dec(E, estado) &
    Estado = promueve &
    G = 12 &
    E = inscripto &
    I_ = [G, Estado] &
    dec(I_, inscripcion) &
    sadd(L, I_, L_) &
    dec(L_, legajo) &
    oplus(Legajos, {[Alumno, L_]}, Legajos_) &
    un(Graduados, {Alumno}, Graduados_).

dec_p_type(cerrarInscripcionEstadoInvalidoE(legajos, alumnos, estado, legajos, alumnos)).
cerrarInscripcionEstadoInvalidoE(Legajos, Graduados, Estado, Legajos_, Graduados_) :-
    Estado = inscripto &
    Legajos_ = Legajos &
    Graduados_ = Graduados.

dec_p_type(cerrarInscripcionAlumnoNoEncontradoE(legajos, alumnos, alumno, legajos, alumnos)).
cerrarInscripcionAlumnoNoEncontradoE(Legajos, Graduados, Alumno, Legajos_, Graduados_) :-
    ninDom(Alumno, Legajos) &
    Legajos_ = Legajos &
    Graduados_ = Graduados.

operation(cerrarInscripcion).
dec_p_type(cerrarInscripcion(legajos, alumnos, alumno, estado, legajos, alumnos)).
cerrarInscripcion(Legajos, Graduados, Alumno, Estado, Legajos_, Graduados_) :-
    cerrarInscripcionNoGraduadoOk(Legajos, Graduados, Alumno, Estado, Legajos_, Graduados_) or
    cerrarInscripcionGraduadoOk(Legajos, Graduados, Alumno, Estado, Legajos_, Graduados_) or
    cerrarInscripcionEstadoInvalidoE(Legajos, Graduados, Estado, Legajos_, Graduados_) or
    cerrarInscripcionAlumnoNoEncontradoE(Legajos, Graduados, Alumno, Legajos_, Graduados_).

dec_p_type(alumnoEsRepitenteSiOk(legajos, alumnos, alumno, rep, legajos, alumnos)).
alumnoEsRepitenteSiOk(Legajos, Graduados, Alumno, Rep, Legajos, Graduados) :-
    inDom(Alumno, Legajos) &
    applyTo(Legajos, Alumno, L) &
    dec(L, legajo) &
    slast(L, I) &
    dec(I, inscripcion) &
    [G, E] = I &
    dec(G, grado) &
    dec(E, estado) &
    E = repite &
    Rep = alumnoEsRepitente.

dec_p_type(alumnoEsRepitenteNoOk(legajos, alumnos, alumno, rep, legajos, alumnos)).
alumnoEsRepitenteNoOk(Legajos, Graduados, Alumno, Rep, Legajos, Graduados) :-
    inDom(Alumno, Legajos) &
    applyTo(Legajos, Alumno, L) &
    dec(L, legajo) &
    slast(L, I) &
    dec(I, inscripcion) &
    [G, E] = I &
    dec(G, grado) &
    dec(E, estado) &
    E neq repite &
    Rep = alumnoNoEsRepitente.

dec_p_type(alumnoEsRepitenteNoEncontradoE(legajos, alumnos, alumno, rep, legajos, alumnos)).
alumnoEsRepitenteNoEncontradoE(Legajos, Graduados, Alumno, Rep, Legajos, Graduados) :-
    ninDom(Alumno, Legajos) &
    Rep = alumnoNoEncontrado.

dec_p_type(alumnoEsRepitente(legajos, alumnos, alumno, rep, legajos, alumnos)).
operation(alumnoEsRepitente).
alumnoEsRepitente(Legajos, Graduados, Alumno, Rep, Legajos, Graduados) :-
    alumnoEsRepitenteSiOk(Legajos, Graduados, Alumno, Rep, Legajos, Graduados) or
    alumnoEsRepitenteNoOk(Legajos, Graduados, Alumno, Rep, Legajos, Graduados) or
    alumnoEsRepitenteNoEncontradoE(Legajos, Graduados, Alumno, Rep, Legajos, Graduados).
