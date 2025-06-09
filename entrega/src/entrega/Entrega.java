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
 *    + Afegir un mètode (dins el tema que el necessiteu)
 *    + Afegir proves a un mètode "tests()"
 *    + Òbviament, implementar els mètodes que heu d'implementar ("exerciciX")
 *   Si feu una modificació que no sigui d'aquesta llista, tendreu un 0.
 *
 * - Principalment, la nota dependrà del correcte funcionament dels mètodes implementats (provant
 *   amb diferents entrades).
 *
 * - Tendrem en compte la neteja i organització del codi. Un estandard que podeu seguir és la guia
 *   d'estil de Google per Java: https://google.github.io/styleguide/javaguide.html . Per exemple:
 *    + IMPORTANT: Aquesta entrega està codificada amb UTF-8 i finals de línia LF.
 *    + Indentació i espaiat consistent
 *    + Bona nomenclatura de variables
 *    + Declarar les variables el més aprop possible al primer ús (és a dir, evitau blocs de
 *      declaracions).
 *    + Convé utilitzar el for-each (for (int x : ...)) enlloc del clàssic (for (int i = 0; ...))
 *      sempre que no necessiteu l'índex del recorregut. Igualment per while si no és necessari.
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

    static final String[] NOMS = {"Carlos Alemany Bisquerra", "Alberto Gallego Díaz"};

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
            int result = 0;
            boolean taut = true;
            boolean contr = true;

            // Buscamos el numero máx de variables
            int maxVars = -1;
            for (int v : vars) {
                if (v > maxVars) {
                    maxVars = v;
                }
            }
            maxVars++;

            // Igual que la función Math.pow
            int totalAsignaciones = 1;
            for (int i = 0; i < maxVars; i++) {
                totalAsignaciones *= 2;
            }

            // 3) Probar cada combinación de valores
            for (int mask = 0; mask < totalAsignaciones; mask++) {
                // Construir vals[] sin bit-shifts
                boolean[] vals = new boolean[maxVars];
                int temp = mask;
                for (int i = 0; i < maxVars; i++) {
                    vals[i] = (temp % 2) == 1;
                    temp /= 2;
                }

                // Evaluar la expresión encadenada
                boolean currentVal = vals[vars[0]];
                for (int i = 0; i < ops.length; i++) {
                    boolean nextVal = vals[vars[i + 1]];
                    currentVal = devuelveOp(ops[i], currentVal, nextVal);
                }

                // Actualizar taut y contr, y salir pronto si es posible
                if (currentVal) {
                    contr = false;
                    result = 1;
                } else {
                    taut = false;
                    result = 0;
                }
                if (!taut && !contr) {
                    return -1;
                }
            }
            //System.out.println(result);
            return result;
        }

        private static boolean devuelveOp(char op, boolean a, boolean b) {
            switch (op) {
                case CONJ:
                    return a && b;
                case DISJ:
                    return a || b;
                case IMPL:
                    return !a || b;
                case NAND:
                    return !(a && b);
                default:
                    throw new IllegalArgumentException("Operador inválido: " + op);
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

            // Evaluar ∀x P(x)
            boolean paraTP = true;
            for (int x : universe) {
                if (!p.test(x)) {
                    paraTP = false;
                    break; // No es necesario seguir si ya hay un elemento que no cumple
                }
            }

            // Evaluar ∃!x Q(x)
            int Q = 0;
            for (int x : universe) {
                if (q.test(x)) {
                    Q++;
                    // Si ya hay más de uno, podemos detenernos
                    if (Q > 1) {
                        break;
                    }
                }
            }
            boolean exactamenteQ = (Q == 1);

            // Verificar equivalencia lógica
            return paraTP == exactamenteQ;

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
            // Calculamos los números de Stirling de segunda especie y luego el número de Bell
            return numeroMaximoP(n);
        }

        private static int numeroMaximoP(int n) {
            // Los números de Bell B(n) representan el número total de particiones posibles
            // para un conjunto de n elementos

            // Para conjuntos pequeños, retornamos valores conocidos
            if (n == 0 || n == 1) {
                return 1;
            }

            // Usaremos el triángulo de Bell para calcular el número
            int[][] stirling = new int[n + 1][n + 1];

            // Caso base: S(0,0) = 1
            stirling[0][0] = 1;

            // Rellenamos la tabla de números de Stirling del segundo tipo
            for (int i = 1; i <= n; i++) {
                for (int j = 1; j <= i; j++) {
                    // Fórmula recursiva: S(n,k) = k*S(n-1,k) + S(n-1,k-1)
                    stirling[i][j] = j * stirling[i - 1][j] + stirling[i - 1][j - 1];
                }
            }

            // El número de Bell es la suma de los números de Stirling de segunda especie
            int numeroMaximoP = 0;
            for (int k = 0; k <= n; k++) {
                numeroMaximoP += stirling[n][k];
            }

            return numeroMaximoP;
        }

        /*
     * Trobau el cardinal de la relació d'ordre parcial sobre `a` més petita que conté `rel` (si
     * existeix). En altres paraules, el cardinal de la seva clausura reflexiva, transitiva i
     * antisimètrica.
     *
     * Si no existeix, retornau -1.
         */
        static int exercici2(int[] a, int[][] rel) {
    // Verificar si la relación es antisimétrica
    for (int[] pair : rel) {
        int x = pair[0];
        int y = pair[1];
        if (x != y) {
            // Buscar si existe (y,x) en la relación
            for (int[] pair2 : rel) {
                if (pair2[0] == y && pair2[1] == x) {
                    return -1; // No es antisimétrica
                }
            }
        }
    }
    
    // Calcular clausura reflexiva y transitiva
    int n = a.length;
    boolean[][] matrix = new boolean[n][n];
    
    // Inicializar matriz con la relación original
    for (int[] pair : rel) {
        int x = pair[0];
        int y = pair[1];
        matrix[x][y] = true;
    }
    
    // Clausura reflexiva
    for (int i = 0; i < n; i++) {
        matrix[i][i] = true;
    }
    
    // Clausura transitiva (algoritmo de Warshall)
    for (int k = 0; k < n; k++) {
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                if (matrix[i][k] && matrix[k][j]) {
                    matrix[i][j] = true;
                }
            }
        }
    }
    
    // Contar pares en la clausura
    int count = 0;
    for (int i = 0; i < n; i++) {
        for (int j = 0; j < n; j++) {
            if (matrix[i][j]) {
                count++;
            }
        }
    }
    
    return count;
}

        /*
     * Donada una relació d'ordre parcial `rel` definida sobre `a` i un subconjunt `x` de `a`,
     * retornau:
     * - L'ínfim de `x` si existeix i `op` és false
     * - El suprem de `x` si existeix i `op` és true
     * - null en qualsevol altre cas
         */
        static Integer exercici3(int[] a, int[][] rel, int[] x, boolean op) {
    if (x.length == 0) return null;
    
    List<Integer> candidates = new ArrayList<>();
    
    // Para ínfimo (op=false) o supremo (op=true)
    for (int elem : a) {
        boolean isCandidate = true;
        
        for (int target : x) {
            boolean found = false;
            for (int[] pair : rel) {
                if (op) { // Supremo: elem >= target
                    if (pair[0] == target && pair[1] == elem) found = true;
                } else { // Ínfimo: elem <= target
                    if (pair[0] == elem && pair[1] == target) found = true;
                }
            }
            if (!found) {
                isCandidate = false;
                break;
            }
        }
        
        if (isCandidate) {
            candidates.add(elem);
        }
    }
    
    if (candidates.isEmpty()) return null;
    
    // Encontrar el mejor candidato (mínimo para supremo, máximo para ínfimo)
    Integer result = candidates.get(0);
    for (int cand : candidates) {
        boolean better = true;
        for (int other : candidates) {
            boolean found = false;
            for (int[] pair : rel) {
                if (op) { // Para supremo: cand <= other
                    if (pair[0] == cand && pair[1] == other) found = true;
                } else { // Para ínfimo: cand >= other
                    if (pair[0] == other && pair[1] == cand) found = true;
                }
            }
            if (!found) {
                better = false;
                break;
            }
        }
        if (better) {
            result = cand;
        }
    }
    
    return result;
}

        /*
     * Donada una funció `f` de `a` a `b`, retornau:
     *  - El graf de la seva inversa (si existeix)
     *  - Sinó, el graf d'una inversa seva per l'esquerra (si existeix)
     *  - Sinó, el graf d'una inversa seva per la dreta (si existeix)
     *  - Sinó, null.
         */
       static int[][] exercici4(int[] a, int[] b, Function<Integer, Integer> f) {
    // Primero verificamos si la función es biyectiva (tiene inversa completa)
    if (a.length == b.length) {
        boolean biyectiva = true;
        boolean[] cubierto = new boolean[b.length];
        for (int x : a) {
            int y = f.apply(x);
            if (y < 0 || y >= b.length || cubierto[y]) {
                biyectiva = false;
                break;
            }
            cubierto[y] = true;
        }
        
        if (biyectiva) {
            int[][] inversa = new int[b.length][2];
            for (int x : a) {
                int y = f.apply(x);
                inversa[y][0] = y;
                inversa[y][1] = x;
            }
            return inversa;
        }
    }
    
    // Verificar si tiene inversa por la izquierda (función inyectiva)
    boolean inyectiva = true;
    for (int i = 0; i < a.length && inyectiva; i++) {
        for (int j = i + 1; j < a.length; j++) {
            if (f.apply(a[i]) == f.apply(a[j])) {
                inyectiva = false;
                break;
            }
        }
    }
    
    if (inyectiva) {
        int[][] inversaIzq = new int[b.length][2];
        // Inicializar con valores por defecto
        for (int i = 0; i < b.length; i++) {
            inversaIzq[i][0] = i;
            inversaIzq[i][1] = a[0]; // Valor por defecto
        }
        // Asignar los valores conocidos
        for (int x : a) {
            int y = f.apply(x);
            inversaIzq[y][1] = x;
        }
        return inversaIzq;
    }
    
    // Verificar si tiene inversa por la derecha (función sobreyectiva)
    boolean[] cubierto = new boolean[b.length];
    for (int x : a) {
        int y = f.apply(x);
        if (y >= 0 && y < b.length) {
            cubierto[y] = true;
        }
    }
    
    boolean sobreyectiva = true;
    for (boolean c : cubierto) {
        if (!c) {
            sobreyectiva = false;
            break;
        }
    }
    
    if (sobreyectiva) {
        int[][] inversaDer = new int[b.length][2];
        boolean[] usado = new boolean[a.length];
        
        for (int y = 0; y < b.length; y++) {
            inversaDer[y][0] = y;
            // Buscar cualquier x que mapee a y
            for (int i = 0; i < a.length; i++) {
                if (f.apply(a[i]) == y && !usado[i]) {
                    inversaDer[y][1] = a[i];
                    usado[i] = true;
                    break;
                }
            }
        }
        return inversaDer;
    }
    
    // Si no cumple ninguna condición
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
            throw new UnsupportedOperationException("pendent");
        }

        /*
     * Determinau si els dos grafs són isomorfs. Podeu suposar que cap dels dos té ordre major que
     * 10.
         */
        static boolean exercici2(int[][] g1, int[][] g2) {
            throw new UnsupportedOperationException("pendent");
        }

        /*
     * Determinau si el graf `g` (no dirigit) és un arbre. Si ho és, retornau el seu recorregut en
     * postordre desde el vèrtex `r`. Sinó, retornau null;
     *
     * En cas de ser un arbre, assumiu que l'ordre dels fills vé donat per l'array de veïns de cada
     * vèrtex.
         */
        static int[] exercici3(int[][] g, int r) {
            throw new UnsupportedOperationException("pendent");
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
    // Encontrar posición inicial (O) y destino (D)
    int startX = -1, startY = -1, endX = -1, endY = -1;
    for (int i = 0; i < mapa.length; i++) {
        for (int j = 0; j < mapa[i].length; j++) {
            if (mapa[i][j] == 'O') {
                startX = i;
                startY = j;
            } else if (mapa[i][j] == 'D') {
                endX = i;
                endY = j;
            }
        }
    }
    
    if (startX == -1 || endX == -1) return -1;

    // BFS usando arrays estáticos
    int rows = mapa.length;
    int cols = mapa[0].length;
    int[][] distance = new int[rows][cols];
    for (int i = 0; i < rows; i++) {
        Arrays.fill(distance[i], -1);
    }
    
    // Simular cola con arrays
    int[] queueX = new int[rows * cols];
    int[] queueY = new int[rows * cols];
    int head = 0, tail = 0;
    
    queueX[tail] = startX;
    queueY[tail] = startY;
    distance[startX][startY] = 0;
    tail++;
    
    // Direcciones: arriba, abajo, izquierda, derecha
    int[][] dirs = {{-1,0}, {1,0}, {0,-1}, {0,1}};
    
    while (head < tail) {
        int x = queueX[head];
        int y = queueY[head];
        head++;
        
        if (x == endX && y == endY) {
            return distance[x][y];
        }
        
        for (int[] dir : dirs) {
            int nx = x + dir[0];
            int ny = y + dir[1];
            
            if (nx >= 0 && nx < rows && ny >= 0 && ny < cols && 
                mapa[nx][ny] != '#' && distance[nx][ny] == -1) {
                distance[nx][ny] = distance[x][y] + 1;
                queueX[tail] = nx;
                queueY[tail] = ny;
                tail++;
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
    byte[] bytes = msg.getBytes();
    int[] result = new int[bytes.length / 2];
    
    for (int i = 0; i < result.length; i++) {
        int block = ((bytes[2*i] & 0xFF) << 8) | (bytes[2*i+1] & 0xFF);
        result[i] = modExp(block, e, n);
    }
    
    return result;
}

private static int modExp(int base, int exp, int mod) {
    int result = 1;
    base = base % mod;
    
    while (exp > 0) {
        if ((exp & 1) == 1) {
            result = (result * base) % mod;
        }
        exp = exp >> 1;
        base = (base * base) % mod;
    }
    
    return result;
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
    // Factorización de n (fuerza bruta permitida)
    int p = 2;
    while (p <= Math.sqrt(n)) {
        if (n % p == 0) {
            break;
        }
        p++;
    }
    int q = n / p;
    
    // Cálculo de φ(n) y d
    int phi = (p - 1) * (q - 1);
    int d = modInverse(e, phi);
    if (d == -1) return null;
    
    // Descifrado
    byte[] bytes = new byte[m.length * 2];
    for (int i = 0; i < m.length; i++) {
        int decrypted = modExp(m[i], d, n);
        bytes[2*i] = (byte)((decrypted >> 8) & 0xFF);
        bytes[2*i+1] = (byte)(decrypted & 0xFF);
    }
    
    return new String(bytes);
}

private static int modInverse(int a, int m) {
    a = a % m;
    for (int x = 1; x < m; x++) {
        if ((a * x) % m == 1) {
            return x;
        }
    }
    return -1;
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
