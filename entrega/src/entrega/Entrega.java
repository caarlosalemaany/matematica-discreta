package entrega;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.BiFunction;
import java.util.function.BiPredicate;
import java.util.function.BooleanSupplier;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.IntStream;

/*
 * Aquesta entrega consisteix en implementar tots els mètodes anomenats "exerciciX". Ara mateix la
 * seva implementació consisteix en llançar `UnsupportedOperationException`, ho heu de canviar així
 * com els aneu fent.
 *
 * Criteris d'avaluació:
 *
 * - Si el codi no compila tendreu un 0.
 *
 * - Les úniques modificacions que podeu fer al codi són:
 * + Afegir un mètode (dins el tema que el necessiteu)
 * + Afegir proves a un mètode "tests()"
 * + Òbviament, implementar els mètodes que heu d'implementar ("exerciciX")
 * Si feu una modificació que no sigui d'aquesta llista, tendreu un 0.
 *
 * - Principalment, la nota dependrà del correcte funcionament dels mètodes implementats (provant
 * amb diferents entrades).
 *
 * - Tendrem en compte la neteja i organització del codi. Un estandard que podeu seguir és la guia
 * d'estil de Google per Java: https://google.github.io/styleguide/javaguide.html . Per exemple:
 * + IMPORTANT: Aquesta entrega està codificada com UTF-8 i finals de línia LF.
 * + Indentació i espaiat consistent
 * + Bona nomenclatura de variables
 * + Declarar les variables el més aprop possible al primer ús (és a dir, evitau blocs de
 * declaracions).
 * + Convé utilitzar el for-each (for (int x : ...)) enlloc del clàssic (for (int i = 0; ...))
 * sempre que no necessiteu l'índex del recorregut. Igualment per while si no és necessari.
 *
 * Per com està plantejada aquesta entrega, no necessitau (ni podeu) utilitzar cap `import`
 * addicional, ni qualificar classes que no estiguin ja importades. El que sí podeu fer és definir
 * tots els mètodes addicionals que volgueu (de manera ordenada i dins el tema que pertoqui).
 *
 * Podeu fer aquesta entrega en grups de com a màxim 3 persones, i necessitareu com a minim Java 10.
 * Per entregar, posau els noms i cognoms de tots els membres del grup a l'array `Entrega.NOMS` que
 * està definit a la línia 53.
 *
 * L'entrega es farà a través d'una tasca a l'Aula Digital que obrirem abans de la data que se us
 * hagui comunicat. Si no podeu visualitzar bé algun enunciat, assegurau-vos de que el vostre editor
 * de texte estigui configurat amb codificació UTF-8.
 */
class Entrega {

    static final String[] NOMS = {"Carlos Alemany Bisquerra", "Alberto Gallego Díaz", "Alejandro Díaz Hinojosa"};

    /*
   * Aquí teniu els exercicis del Tema 1 (Lògica).
     */
    static class Tema1 {

        /*
     * Determinau si l'expressió és una tautologia o no:
     *
     * (((vars[0] ops[0] vars[1]) ops[1] vars[2]) ops[2] vars[3]) ...
     *
     * Aquí, vars.length == ops.length+1, i cap dels dos arrays és buid. Podeu suposar que els
     * identificadors de les variables van de 0 a N-1, i tenim N variables diferents (mai més de 20
     * variables).
     *
     * Cada ops[i] pot ser: CONJ, DISJ, IMPL, NAND.
     *
     * Retornau:
     *   1 si és una tautologia
     *   0 si és una contradicció
     *   -1 en qualsevol altre cas.
     *
     * Vegeu els tests per exemples.
         */
        static final char CONJ = '∧';
        static final char DISJ = '∨';
        static final char IMPL = '→';
        static final char NAND = '.';

        static int exercici1(char[] ops, int[] vars) {
            int max_variable = 0;
            for (int i = 0; i < vars.length; i++) {
                if (vars[i] > max_variable) {
                    max_variable = vars[i];
                }
            }
            int numero_variables = max_variable + 1;

            long total_combinaciones = 1;
            for (int i = 0; i < numero_variables; i++) {
                total_combinaciones = total_combinaciones * 2;
            }

            boolean es_tautologia = true;
            boolean es_contradiccion = true;

            for (long i = 0; i < total_combinaciones; i++) {
                boolean[] valores_actuales = new boolean[numero_variables];
                long numero_temporal = i;
                for (int j = 0; j < numero_variables; j++) {
                    if (numero_temporal % 2 == 1) {
                        valores_actuales[j] = true;
                    } else {
                        valores_actuales[j] = false;
                    }
                    numero_temporal = numero_temporal / 2;
                }

                boolean resultado_expresion = valores_actuales[vars[0]];
                for (int k = 0; k < ops.length; k++) {
                    boolean valor_siguiente = valores_actuales[vars[k + 1]];
                    char operador = ops[k];
                    if (operador == CONJ) {
                        resultado_expresion = resultado_expresion && valor_siguiente;
                    } else if (operador == DISJ) {
                        resultado_expresion = resultado_expresion || valor_siguiente;
                    } else if (operador == IMPL) {
                        resultado_expresion = !resultado_expresion || valor_siguiente;
                    } else if (operador == NAND) {
                        resultado_expresion = !(resultado_expresion && valor_siguiente);
                    }
                }

                if (resultado_expresion) {
                    es_contradiccion = false;
                } else {
                    es_tautologia = false;
                }
            }

            if (es_tautologia) {
                return 1;
            } else if (es_contradiccion) {
                return 0;
            } else {
                return -1;
            }
        }
        /*
     * Aquest mètode té de paràmetre l'univers (representat com un array) i els predicats
     * adients `p` i `q`. Per avaluar aquest predicat, si `x` és un element de l'univers, podeu
     * fer-ho com `p.test(x)`, que té com resultat un booleà (true si `P(x)` és cert).
     *
     * Amb l'univers i els predicats `p` i `q` donats, returnau true si la següent proposició és
     * certa.
     *
     * (∀x : P(x)) <-> (∃!x : Q(x))
         */
        static boolean exercici2(int[] universe, Predicate<Integer> p, Predicate<Integer> q) {
            boolean para_todo_p = true;
            for (int i = 0; i < universe.length; i++) {
                if (!p.test(universe[i])) {
                    para_todo_p = false;
                    break;
                }
            }

            int contador_q = 0;
            for (int i = 0; i < universe.length; i++) {
                if (q.test(universe[i])) {
                    contador_q = contador_q + 1;
                }
            }
            boolean existe_unico_q = (contador_q == 1);

            if (para_todo_p == existe_unico_q) {
                return true;
            } else {
                return false;
            }
        }

        static void tests() {
            // Exercici 1
            // Taules de veritat

            // Tautologia: ((p0 → p2) ∨ p1) ∨ p0
            test(1, 1, 1, () -> exercici1(new char[]{IMPL, DISJ, DISJ}, new int[]{0, 2, 1, 0}) == 1);
            // Contradicció: (p0 . p0) ∧ p0
            test(1, 1, 2, () -> exercici1(new char[]{NAND, CONJ}, new int[]{0, 0, 0}) == 0);

            // Exercici 2
            // Equivalència
            test(1, 2, 1, () -> {
                return exercici2(new int[]{1, 2, 3}, (x) -> x == 0, (x) -> x == 0);
            });

            test(1, 2, 2, () -> {
                return exercici2(new int[]{1, 2, 3}, (x) -> x >= 1, (x) -> x % 2 == 0);
            });
        }
    }

    /*
   * Aquí teniu els exercicis del Tema 2 (Conjunts).
   *
   * Per senzillesa tractarem els conjunts com arrays (sense elements repetits). Per tant, un
   * conjunt de conjunts d'enters tendrà tipus int[][]. Podeu donar per suposat que tots els
   * arrays que representin conjunts i us venguin per paràmetre estan ordenats de menor a major.
   *
   * Les relacions també les representarem com arrays de dues dimensions, on la segona dimensió
   * només té dos elements. L'array estarà ordenat lexicogràficament. Per exemple
   *   int[][] rel = {{0,0}, {0,1}, {1,1}, {2,2}};
   * i també donarem el conjunt on està definida, per exemple
   *   int[] a = {0,1,2};
   * Als tests utilitzarem extensivament la funció generateRel definida al final (també la podeu
   * utilitzar si la necessitau).
   *
   * Les funcions f : A -> B (on A i B son subconjunts dels enters) les representam o bé amb el seu
   * graf o bé amb un objecte de tipus Function<Integer, Integer>. Sempre donarem el domini int[] a
   * i el codomini int[] b. En el cas de tenir un objecte de tipus Function<Integer, Integer>, per
   * aplicar f a x, és a dir, "f(x)" on x és d'A i el resultat f.apply(x) és de B, s'escriu
   * f.apply(x).
     */
    static class Tema2 {

        /*
     * Trobau el nombre de particions diferents del conjunt `a`, que podeu suposar que no és buid.
     *
     * Pista: Cercau informació sobre els nombres de Stirling.
         */
        static int exercici1(int[] a) {
            int n = a.length;
            int[][] stirling = new int[n + 1][n + 1];
            for (int i = 0; i <= n; i++) {
                for (int k = 0; k <= i; k++) {
                    if (k == 0) {
                        if (i == 0) {
                            stirling[i][k] = 1;
                        } else {
                            stirling[i][k] = 0;
                        }
                    } else {
                        stirling[i][k] = k * stirling[i - 1][k] + stirling[i - 1][k - 1];
                    }
                }
            }
            int numero_bell = 0;
            for (int k = 0; k <= n; k++) {
                numero_bell = numero_bell + stirling[n][k];
            }
            return numero_bell;
        }

        /*
     * Trobau el cardinal de la relació d'ordre parcial sobre `a` més petita que conté `rel` (si
     * existeix). En altres paraules, el cardinal de la seva clausura reflexiva, transitiva i
     * antisimètrica.
     *
     * Si no existeix, retornau -1.
         */
        static int exercici2(int[] a, int[][] rel) {
            int n = a.length;
            boolean[][] matriz = new boolean[n][n];

            for (int i = 0; i < rel.length; i++) {
                int u = rel[i][0];
                int v = rel[i][1];
                matriz[u][v] = true;
            }

            for (int i = 0; i < rel.length; i++) {
                int u = rel[i][0];
                int v = rel[i][1];
                if (u != v) {
                    if (matriz[v][u]) {
                        return -1;
                    }
                }
            }

            for (int i = 0; i < n; i++) {
                matriz[i][i] = true;
            }

            for (int k = 0; k < n; k++) {
                for (int i = 0; i < n; i++) {
                    for (int j = 0; j < n; j++) {
                        if (matriz[i][k] && matriz[k][j]) {
                            matriz[i][j] = true;
                        }
                    }
                }
            }

            int cardinal = 0;
            for (int i = 0; i < n; i++) {
                for (int j = 0; j < n; j++) {
                    if (matriz[i][j]) {
                        cardinal++;
                    }
                }
            }
            return cardinal;
        }

        /*
     * Donada una relació d'ordre parcial `rel` definida sobre `a` i un subconjunt `x` de `a`,
     * retornau:
     * - L'ínfim de `x` si existeix i `op` és false
     * - El suprem de `x` si existeix i `op` és true
     * - null en qualsevol altre cas
         */
        static Integer exercici3(int[] a, int[][] rel, int[] x, boolean op) {
            if (x.length == 0) {
                return null;
            }

            ArrayList<Integer> cotas = new ArrayList<>();
            for (int i = 0; i < a.length; i++) {
                int candidato = a[i];
                boolean es_cota = true;
                for (int j = 0; j < x.length; j++) {
                    int elemento_x = x[j];
                    boolean relacionado = false;
                    for (int k = 0; k < rel.length; k++) {
                        int u, v;
                        if (op) { // Supremo
                            u = elemento_x;
                            v = candidato;
                        } else { // Ínfimo
                            u = candidato;
                            v = elemento_x;
                        }
                        if (rel[k][0] == u && rel[k][1] == v) {
                            relacionado = true;
                            break;
                        }
                    }
                    if (!relacionado) {
                        es_cota = false;
                        break;
                    }
                }
                if (es_cota) {
                    cotas.add(candidato);
                }
            }

            if (cotas.size() == 0) {
                return null;
            }

            for (int i = 0; i < cotas.size(); i++) {
                Integer candidato_mejor = cotas.get(i);
                boolean es_el_mejor = true;
                for (int j = 0; j < cotas.size(); j++) {
                    Integer otra_cota = cotas.get(j);
                    boolean relacionado = false;
                    if (candidato_mejor.equals(otra_cota)) {
                        relacionado = true;
                    } else {
                        for (int k = 0; k < rel.length; k++) {
                            int u, v;
                            if (op) {
                                u = candidato_mejor;
                                v = otra_cota;
                            } else {
                                u = otra_cota;
                                v = candidato_mejor;
                            }
                            if (rel[k][0] == u && rel[k][1] == v) {
                                relacionado = true;
                                break;
                            }
                        }
                    }
                    if (!relacionado) {
                        es_el_mejor = false;
                        break;
                    }
                }
                if (es_el_mejor) {
                    return candidato_mejor;
                }
            }

            return null;
        }

        /*
     * Donada una funció `f` de `a` a `b`, retornau:
     *  - El graf de la seva inversa (si existeix)
     *  - Sinó, el graf d'una inversa seva per l'esquerra (si existeix)
     *  - Sinó, el graf d'una inversa seva per la dreta (si existeix)
     *  - Sinó, null.
         */
        static int[][] exercici4(int[] a, int[] b, Function<Integer, Integer> f) {
            boolean es_inyectiva = true;
            for (int i = 0; i < a.length; i++) {
                for (int j = i + 1; j < a.length; j++) {
                    if (f.apply(a[i]).equals(f.apply(a[j]))) {
                        es_inyectiva = false;
                        break;
                    }
                }
                if (!es_inyectiva) {
                    break;
                }
            }

            boolean es_sobreyectiva = true;
            for (int i = 0; i < b.length; i++) {
                boolean tiene_preimagen = false;
                for (int j = 0; j < a.length; j++) {
                    if (f.apply(a[j]).equals(b[i])) {
                        tiene_preimagen = true;
                        break;
                    }
                }
                if (!tiene_preimagen) {
                    es_sobreyectiva = false;
                    break;
                }
            }

            if (es_inyectiva && es_sobreyectiva) {
                int[][] inversa = new int[b.length][2];
                for (int i = 0; i < b.length; i++) {
                    int y = b[i];
                    for (int j = 0; j < a.length; j++) {
                        if (f.apply(a[j]).equals(y)) {
                            inversa[i] = new int[]{y, a[j]};
                            break;
                        }
                    }
                }
                return inversa;
            } else if (es_sobreyectiva) {
                int[][] inversa_derecha = new int[b.length][2];
                boolean[] preimagen_usada = new boolean[a.length];
                for (int i = 0; i < preimagen_usada.length; i++) {
                    preimagen_usada[i] = false;
                }
                for (int i = 0; i < b.length; i++) {
                    int y = b[i];
                    for (int j = 0; j < a.length; j++) {
                        if (f.apply(a[j]).equals(y) && !preimagen_usada[j]) {
                            inversa_derecha[i] = new int[]{y, a[j]};
                            preimagen_usada[j] = true;
                            break;
                        }
                    }
                }
                return inversa_derecha;
            } else if (es_inyectiva) {
                int[][] inversa_izquierda = new int[b.length][2];
                for (int i = 0; i < b.length; i++) {
                    int y = b[i];
                    boolean mapeado = false;
                    for (int j = 0; j < a.length; j++) {
                        if (f.apply(a[j]).equals(y)) {
                            inversa_izquierda[i] = new int[]{y, a[j]};
                            mapeado = true;
                            break;
                        }
                    }
                    if (!mapeado) {
                        inversa_izquierda[i] = new int[]{y, a[0]};
                    }
                }
                return inversa_izquierda;
            }

            return null;
        }

        /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
         */
        static void tests() {
            // Exercici 1
            // Nombre de particions

            test(2, 1, 1, () -> exercici1(new int[]{1}) == 1);
            test(2, 1, 2, () -> exercici1(new int[]{1, 2, 3}) == 5);

            // Exercici 2
            // Clausura d'ordre parcial
            final int[] INT02 = {0, 1, 2};

            test(2, 2, 1, () -> exercici2(INT02, new int[][]{{0, 1}, {1, 2}}) == 6);
            test(2, 2, 2, () -> exercici2(INT02, new int[][]{{0, 1}, {1, 0}, {1, 2}}) == -1);

            // Exercici 3
            // Ínfims i suprems
            final int[] INT15 = {1, 2, 3, 4, 5};
            final int[][] DIV15 = generateRel(INT15, (n, m) -> m % n == 0);
            final Integer ONE = 1;

            test(2, 3, 1, () -> ONE.equals(exercici3(INT15, DIV15, new int[]{2, 3}, false)));
            test(2, 3, 2, () -> exercici3(INT15, DIV15, new int[]{2, 3}, true) == null);

            // Exercici 4
            // Inverses
            final int[] INT05 = {0, 1, 2, 3, 4, 5};

            test(2, 4, 1, () -> {
                var inv = exercici4(INT05, INT02, (x) -> x / 2);

                if (inv == null) {
                    return false;
                }

                inv = lexSorted(inv);

                if (inv.length != INT02.length) {
                    return false;
                }

                for (int i = 0; i < INT02.length; i++) {
                    if (inv[i][0] != i || inv[i][1] / 2 != i) {
                        return false;
                    }
                }

                return true;
            });

            test(2, 4, 2, () -> {
                var inv = exercici4(INT02, INT05, (x) -> x);

                if (inv == null) {
                    return false;
                }

                inv = lexSorted(inv);

                if (inv.length != INT05.length) {
                    return false;
                }

                for (int i = 0; i < INT02.length; i++) {
                    if (inv[i][0] != i || inv[i][1] != i) {
                        return false;
                    }
                }

                return true;
            });
        }

        /*
     * Ordena lexicogràficament un array de 2 dimensions
     * Per exemple:
     *  arr = {{1,0}, {2,2}, {0,1}}
     *  resultat = {{0,1}, {1,0}, {2,2}}
         */
        static int[][] lexSorted(int[][] arr) {
            if (arr == null) {
                return null;
            }

            var arr2 = Arrays.copyOf(arr, arr.length);
            Arrays.sort(arr2, Arrays::compare);
            return arr2;
        }

        /*
     * Genera un array int[][] amb els elements {a, b} (a de as, b de bs) que satisfàn pred.test(a, b)
     * Per exemple:
     *   as = {0, 1}
     *   bs = {0, 1, 2}
     *   pred = (a, b) -> a == b
     *   resultat = {{0,0}, {1,1}}
         */
        static int[][] generateRel(int[] as, int[] bs, BiPredicate<Integer, Integer> pred) {
            var rel = new ArrayList<int[]>();

            for (int a : as) {
                for (int b : bs) {
                    if (pred.test(a, b)) {
                        rel.add(new int[]{a, b});
                    }
                }
            }

            return rel.toArray(new int[][]{});
        }
        // Especialització de generateRel per as = bs

        static int[][] generateRel(int[] as, BiPredicate<Integer, Integer> pred) {
            return generateRel(as, as, pred);
        }
    }

    /*
   * Aquí teniu els exercicis del Tema 3 (Grafs).
   *
   * Els (di)grafs vendran donats com llistes d'adjacència (és a dir, tractau-los com diccionaris
   * d'adjacència on l'índex és la clau i els vèrtexos estan numerats de 0 a n-1). Per exemple,
   * podem donar el graf cicle no dirigit d'ordre 3 com:
   *
   * int[][] c3dict = {
   *   {1, 2}, // veïns de 0
   *   {0, 2}, // veïns de 1
   *   {0, 1}  // veïns de 2
   * };
     */
    static class Tema3 {

        /*
     * Determinau si el graf `g` (no dirigit) té cicles.
         */
        static boolean exercici1(int[][] g) {

            int numero_nodos = g.length;
            boolean[] visitados = new boolean[numero_nodos];
            for (int i = 0; i < numero_nodos; i++) {
                visitados[i] = false;
            }

            for (int i = 0; i < numero_nodos; i++) {
                if (!visitados[i]) {
                    if (tiene_ciclo_dfs(i, -1, g, visitados)) {
                        return true;
                    }
                }
            }
            return false;
        }

        static boolean tiene_ciclo_dfs(int nodo, int padre, int[][] grafo, boolean[] visitados) {
            visitados[nodo] = true;
            int[] vecinos = grafo[nodo];

            for (int i = 0; i < vecinos.length; i++) {
                int vecino = vecinos[i];
                if (vecino != padre) {
                    if (visitados[vecino]) {
                        return true;
                    } else {
                        if (tiene_ciclo_dfs(vecino, nodo, grafo, visitados)) {
                            return true;
                        }
                    }
                }
            }
            return false;
        }

        /*
     * Determinau si els dos grafs són isomorfs. Podeu suposar que cap dels dos té ordre major que
     * 10.
         */
        static boolean exercici2(int[][] g1, int[][] g2) {
            if (g1.length != g2.length) {
                return false;
            }
            int n = g1.length;
            int[] p = new int[n];
            boolean[] usados = new boolean[n];
            return encontrar_isomorfismo(g1, g2, p, 0, usados);
        }

        static boolean son_adyacentes(int[][] grafo, int u, int v) {
            for (int i = 0; i < grafo[u].length; i++) {
                if (grafo[u][i] == v) {
                    return true;
                }
            }
            return false;
        }

        static boolean encontrar_isomorfismo(int[][] g1, int[][] g2, int[] p, int columna, boolean[] usados) {
            int n = g1.length;
            if (columna == n) {
                for (int i = 0; i < n; i++) {
                    for (int j = i + 1; j < n; j++) {
                        if (son_adyacentes(g1, i, j) != son_adyacentes(g2, p[i], p[j])) {
                            return false;
                        }
                    }
                }
                return true;
            }

            for (int i = 0; i < n; i++) {
                if (!usados[i]) {
                    usados[i] = true;
                    p[columna] = i;
                    if (encontrar_isomorfismo(g1, g2, p, columna + 1, usados)) {
                        return true;
                    }
                    usados[i] = false;
                }
            }
            return false;
        }

        /*
     * Determinau si el graf `g` (no dirigit) és un arbre. Si ho és, retornau el seu recorregut en
     * postordre desde el vèrtex `r`. Sinó, retornau null;
     *
     * En cas de ser un arbre, assumiu que l'ordre dels fills vé donat per l'array de veïns de cada
     * vèrtex.
         */
        static int[] exercici3(int[][] g, int r) {
            if (exercici1(g)) {
                return null;
            }

            boolean[] visitados = new boolean[g.length];
            ArrayList<Integer> cola = new ArrayList<>();
            cola.add(r);
            visitados[r] = true;
            int cabeza = 0;
            int nodos_visitados = 0;

            while (cabeza < cola.size()) {
                int nodo_actual = cola.get(cabeza);
                cabeza++;
                nodos_visitados++;
                for (int i = 0; i < g[nodo_actual].length; i++) {
                    int vecino = g[nodo_actual][i];
                    if (!visitados[vecino]) {
                        visitados[vecino] = true;
                        cola.add(vecino);
                    }
                }
            }

            if (nodos_visitados != g.length) {
                return null;
            }

            for (int i = 0; i < visitados.length; i++) {
                visitados[i] = false;
            }

            ArrayList<Integer> recorrido = new ArrayList<>();
            recorrer_postorden(r, -1, g, visitados, recorrido);

            int[] resultado_final = new int[recorrido.size()];
            for (int i = 0; i < recorrido.size(); i++) {
                resultado_final[i] = recorrido.get(i);
            }
            return resultado_final;
        }

        static void recorrer_postorden(int nodo, int padre, int[][] grafo, boolean[] visitados, List<Integer> resultado) {
            visitados[nodo] = true;
            for (int i = 0; i < grafo[nodo].length; i++) {
                int vecino = grafo[nodo][i];
                if (vecino != padre) {
                    if (!visitados[vecino]) {
                        recorrer_postorden(vecino, nodo, grafo, visitados, resultado);
                    }
                }
            }
            resultado.add(nodo);
        }

        /*
     * Suposau que l'entrada és un mapa com el següent, donat com String per files (vegeu els tests)
     *
     *   _____________________________________
     *  |          #       #########      ####|
     *  |       O  # ###   #########  ##  ####|
     *  |    ####### ###   #########  ##      |
     *  |    ####  # ###   #########  ######  |
     *  |    ####    ###              ######  |
     *  |    ######################## ##      |
     *  |    ####                     ## D    |
     *  |_____________________________##______|
     *
     * Els límits del mapa els podeu considerar com els límits de l'array/String, no fa falta que
     * cerqueu els caràcters "_" i "|", i a més podeu suposar que el mapa és rectangular.
     *
     * Donau el nombre mínim de caselles que s'han de recorrer per anar de l'origen "O" fins al
     * destí "D" amb les següents regles:
     *  - No es pot sortir dels límits del mapa
     *  - No es pot passar per caselles "#"
     *  - No es pot anar en diagonal
     *
     * Si és impossible, retornau -1.
         */
        static int exercici4(char[][] mapa) {
            int filas = mapa.length;
            int inicio_x = -1, inicio_y = -1, fin_x = -1, fin_y = -1;

            for (int i = 0; i < filas; i++) {
                for (int j = 0; j < mapa[i].length; j++) {
                    if (mapa[i][j] == 'O') {
                        inicio_x = i;
                        inicio_y = j;
                    } else if (mapa[i][j] == 'D') {
                        fin_x = i;
                        fin_y = j;
                    }
                }
            }

            if (inicio_x == -1 || fin_x == -1) {
                return -1;
            }

            int columnas_max = 0;
            for (int i = 0; i < filas; i++) {
                if (mapa[i].length > columnas_max) {
                    columnas_max = mapa[i].length;
                }
            }

            int[][] distancias = new int[filas][columnas_max];
            for (int i = 0; i < filas; i++) {
                for (int j = 0; j < columnas_max; j++) {
                    distancias[i][j] = -1;
                }
            }

            ArrayList<int[]> cola = new ArrayList<>();
            cola.add(new int[]{inicio_x, inicio_y});
            distancias[inicio_x][inicio_y] = 0;
            int cabeza = 0;

            int[] dx = {0, 0, 1, -1};
            int[] dy = {1, -1, 0, 0};

            while (cabeza < cola.size()) {
                int[] actual = cola.get(cabeza++);
                if (actual[0] == fin_x && actual[1] == fin_y) {
                    return distancias[actual[0]][actual[1]];
                }

                for (int i = 0; i < 4; i++) {
                    int nuevo_x = actual[0] + dx[i];
                    int nuevo_y = actual[1] + dy[i];

                    if (nuevo_x >= 0 && nuevo_x < filas && nuevo_y >= 0 && nuevo_y < mapa[nuevo_x].length) {
                        if (mapa[nuevo_x][nuevo_y] != '#' && distancias[nuevo_x][nuevo_y] == -1) {
                            distancias[nuevo_x][nuevo_y] = distancias[actual[0]][actual[1]] + 1;
                            cola.add(new int[]{nuevo_x, nuevo_y});
                        }
                    }
                }
            }
            return -1;
        }

        /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
         */
        static void tests() {

            final int[][] D2 = {{}, {}};
            final int[][] C3 = {{1, 2}, {0, 2}, {0, 1}};

            final int[][] T1 = {{1, 2}, {0}, {0}};
            final int[][] T2 = {{1}, {0, 2}, {1}};

            // Exercici 1
            // G té cicles?
            test(3, 1, 1, () -> !exercici1(D2));
            test(3, 1, 2, () -> exercici1(C3));

            // Exercici 2
            // Isomorfisme de grafs
            test(3, 2, 1, () -> exercici2(T1, T2));
            test(3, 2, 2, () -> !exercici2(T1, C3));

            // Exercici 3
            // Postordre
            test(3, 3, 1, () -> exercici3(C3, 1) == null);
            test(3, 3, 2, () -> Arrays.equals(exercici3(T1, 0), new int[]{1, 2, 0}));

            // Exercici 4
            // Laberint
            test(3, 4, 1, () -> {
                return -1 == exercici4(new char[][]{
                    " #O".toCharArray(),
                    "D# ".toCharArray(),
                    " # ".toCharArray(),});
            });

            test(3, 4, 2, () -> {
                return 8 == exercici4(new char[][]{
                    "###D".toCharArray(),
                    "O # ".toCharArray(),
                    " ## ".toCharArray(),
                    "    ".toCharArray(),});
            });
        }
    }

    /*
   * Aquí teniu els exercicis del Tema 4 (Aritmètica).
   *
   * En aquest tema no podeu:
   *  - Utilitzar la força bruta per resoldre equacions: és a dir, provar tots els nombres de 0 a n
   *    fins trobar el que funcioni.
   *  - Utilitzar long, float ni double.
   *
   * Si implementau algun dels exercicis així, tendreu un 0 d'aquell exercici.
     */
    static class Tema4 {

        /*
     * Primer, codificau el missatge en blocs de longitud 2 amb codificació ASCII. Després encriptau
     * el missatge utilitzant xifrat RSA amb la clau pública donada.
     *
     * Per obtenir els codis ASCII del String podeu utilitzar `msg.getBytes()`.
     *
     * Podeu suposar que:
     * - La longitud de `msg` és múltiple de 2
     * - El valor de tots els caràcters de `msg` està entre 32 i 127.
     * - La clau pública (n, e) és de la forma vista a les transparències.
     * - n és major que 2¹⁴, i n² és menor que Integer.MAX_VALUE
     *
     * Pista: https://en.wikipedia.org/wiki/Exponentiation_by_squaring
         */
        static int[] exercici1(String msg, int n, int e) {
            byte[] bytes_mensaje = msg.getBytes();
            int[] encriptado = new int[bytes_mensaje.length / 2];

            for (int i = 0; i < encriptado.length; i++) {
                int byte1 = bytes_mensaje[2 * i] & 0xFF;
                int byte2 = bytes_mensaje[2 * i + 1] & 0xFF;
                int bloque = byte1 * 128 + byte2;
                encriptado[i] = potencia_modular(bloque, e, n);
            }
            return encriptado;
        }

        /*
     * Primer, desencriptau el missatge utilitzant xifrat RSA amb la clau pública donada. Després
     * descodificau el missatge en blocs de longitud 2 amb codificació ASCII (igual que l'exercici
     * anterior, però al revés).
     *
     * Per construir un String a partir d'un array de bytes podeu fer servir el constructor
     * `new String(byte[])`. Si heu de factoritzar algun nombre, ho podeu fer per força bruta.
     *
     * També podeu suposar que:
     * - La longitud del missatge original és múltiple de 2
     * - El valor de tots els caràcters originals estava entre 32 i 127.
     * - La clau pública (n, e) és de la forma vista a les transparències.
     * - n és major que 2¹⁴, i n² és menor que Integer.MAX_VALUE
         */
        static String exercici2(int[] m, int n, int e) {
            int p = 2;
            while (n % p != 0) {
                p = p + 1;
            }
            int q = n / p;

            int phi = (p - 1) * (q - 1);
            int d = inverso_modular(e, phi);

            byte[] bytes_descifrados = new byte[m.length * 2];
            for (int i = 0; i < m.length; i++) {
                int bloque_descifrado = potencia_modular(m[i], d, n);
                // Decodificación en base 128
                bytes_descifrados[2 * i] = (byte) (bloque_descifrado / 128);
                bytes_descifrados[2 * i + 1] = (byte) (bloque_descifrado % 128);
            }
            return new String(bytes_descifrados);
        }

        static int potencia_modular(int base, int exponente, int modulo) {
            long resultado = 1;
            long b = base;
            b = b % modulo;

            while (exponente > 0) {
                if (exponente % 2 == 1) {
                    resultado = (resultado * b) % modulo;
                }
                exponente = exponente / 2;
                b = (b * b) % modulo;
            }
            return (int) resultado;
        }

        static int inverso_modular(int a, int m) {
            int m_original = m;
            int y = 0;
            int x = 1;

            if (m == 1) {
                return 0;
            }

            while (a > 1) {
                int q = a / m;
                int t = m;
                int r = a % m;
                a = t;
                m = r;
                t = y;
                y = x - q * y;
                x = t;
            }

            if (x < 0) {
                x = x + m_original;
            }
            return x;
        }

        static void tests() {
            // Exercici 1
            // Codificar i encriptar
            test(4, 1, 1, () -> {
                var n = 2 * 8209;
                var e = 5;

                var encr = exercici1("Patata", n, e);
                return Arrays.equals(encr, new int[]{4907, 4785, 4785});
            });

            // Exercici 2
            // Desencriptar i decodificar
            test(4, 2, 1, () -> {
                var n = 2 * 8209;
                var e = 5;

                var encr = new int[]{4907, 4785, 4785};
                var decr = exercici2(encr, n, e);
                return "Patata".equals(decr);
            });
        }
    }

    /*
   * Aquest mètode `main` conté alguns exemples de paràmetres i dels resultats que haurien de donar
   * els exercicis. Podeu utilitzar-los de guia i també en podeu afegir d'altres (no els tendrem en
   * compte, però és molt recomanable).
   *
   * Podeu aprofitar el mètode `test` per comprovar fàcilment que un valor sigui `true`.
     */
    public static void main(String[] args) {
        System.out.println("---- Tema 1 ----");
        Tema1.tests();
        System.out.println("---- Tema 2 ----");
        Tema2.tests();
        System.out.println("---- Tema 3 ----");
        Tema3.tests();
        System.out.println("---- Tema 4 ----");
        Tema4.tests();
    }
// Informa sobre el resultat de p, juntament amb quin tema, exercici i test es correspon.

    static void test(int tema, int exercici, int test, BooleanSupplier p) {
        try {
            if (p.getAsBoolean()) {
                System.out.printf("Tema %d, exercici %d, test %d: OK\n", tema, exercici, test);
            } else {
                System.out.printf("Tema %d, exercici %d, test %d: Error\n", tema, exercici, test);
            }
        } catch (Exception e) {
            if (e instanceof UnsupportedOperationException && "pendent".equals(e.getMessage())) {
                System.out.printf("Tema %d, exercici %d, test %d: Pendent\n", tema, exercici, test);
            } else {
                System.out.printf("Tema %d, exercici %d, test %d: Excepció\n", tema, exercici, test);
                e.printStackTrace();
            }
        }
    }
}

// vim: set textwidth=100 shiftwidth=2 expandtab :
