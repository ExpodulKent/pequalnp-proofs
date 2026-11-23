"""
L-meta-650. Exakt grindminimum för block om två eller tre linjer.

Kör med Python 3.10 eller senare. Standardbiblioteket räcker. Med ett block
menas en krets som från råa punktsignaler och valda linjesignaler ensam
beräknar incidensfunktionen för just dessa linjer. Ett alternativ som
återanvänder signaler från andra linjer kan fortfarande spara grindar i
kretsen med alla 13 linjer.

Handargument

1. En linje med fyra punkter kostar tre OR och ett AND. En OR av k sådana
   linjetermer kostar 5k-1 grindar. Punkter som enbart hör till samma valda
   linje kan samlas till en enda variabel. För den undre gränsen sätter vi
   alla utom en sådan punkt till 0. Inför varje fixering är punkten väsentlig.
   Minst en grind läser alltså punkten. OR med 0 kan förbigås och AND med 0
   kan ersättas med 0. Efter konstantförenkling har minst en grind försvunnit.
   Därför skulle en besparing i det stora blocket överleva komprimeringen.

   Två linjer delar en skärningspunkt och har vardera tre egna punkter.
   Vi tar bort fyra egna punkter totalt. Kvar blir en stig med fem hörn.
   En besparing skulle ge högst fyra grindar. Tre linjer genom samma punkt
   har också tre egna punkter vardera. När sex punkter tas bort återstår
   tre armar med två kanter vardera, sju hörn och högst sju grindar vid
   en besparing. När de tre skärningspunkterna är olika har varje linje
   två egna punkter. Vi tar bort tre punkter och får en sexcykel med ett
   extra löv på vartannat hörn. En besparing ger högst tio grindar för nio
   variabler. De tre gränserna medger därför noll, en respektive två extra
   trådanvändningar enligt nästa punkt.

2. Rensa bort konstanta grindar, kopior, oanvända grindar och dubbla operander.
   Detta kan göras i en minsta monoton krets för dessa icke-konstanta funktioner.
   En återstående grind har två ingångar. Med n väsentliga insignaler och g
   grindar finns 2g operandförekomster och n+g-1 trådar som måste användas
   minst en gång. Antalet användningar utöver den första är alltså g-n+1.

3. Varje korrekt formel måste upprepa minst ena variabeln på varje kant uv
   som ligger i mitten av en inducerad stig a-u-v-b på fyra hörn. Sätt de
   andra variablerna till 0. När a=b=0 blir funktionen u AND v, när a=b=1
   blir den u OR v. Om u och v förekom en gång var skulle deras lägsta
   gemensamma förfader ha samma grind i båda fallen. Varje sidogren på
   stigarna från löven till roten blir konstant. För att behålla båda
   variablerna måste grindarna på vardera stigen vidarebefordra den
   icke-konstanta signalen. Det ger samma tvåvariabelfunktion i båda fallen.

4. Antag att en förbunden graf saknar två hörn med samma grannmängd.
   Ingen äkta delmängd D av minst två variabler kan då lämna sitt bidrag
   till kantfunktionen genom en enda boolesk signal. Om D innehåller en kant,
   ger tre val på D tre skilda funktioner av de yttre variablerna. Alla
   D-bitar noll lämnar yttergrafens kantfunktion. En inre kant gör svaret
   konstant sant. En ensam ändpunkt till en gränskant ger dessutom utslag
   om enbart dess yttre granne är tänd. Om D är oberoende skiljer vi i stället
   alla nollor och två ensamma D-hörn genom deras olika, icke-tomma yttre
   grannmängder.

5. Den första delade inre grinden H i topologisk ordning måste därför också
   ha en tidigare delad råsignal som bidrar på en väg utanför H. Annars har
   H ett eget block D enligt punkt 4. Om den inre kretsen endast innehåller
   en enda distinkt insignal beräknar H den signalen, eftersom varje AND/OR
   av kopior av samma bit är biten själv. Då kan H förbigås i en mindre krets.
   Om H innehåller alla insignaler skulle utgången enbart bero på H. En
   icke-konstant monoton enbitsfunktion är identiteten, så utgången kan
   ersättas med H och de senare grindarna tas bort.

   Vid högst en extra användning följer att alla upprepningar sitter vid
   råa insignaler. Kretsen kan då sökas som en läs-en-gång-formel, med
   möjligen en extra lövförekomst av en av variablerna.

6. Vid högst två extra användningar finns två möjligheter. Med endast
   upprepade råsignaler har formeln högst två upprepade variabler. Med en
   delad inre grind H finns exakt en delad råsignal u, en inre grind med två
   konsumenter och inget ytterligare omtag. En av u:s vägar går in i H och
   den andra utanför H. H är en läs-en-gång-formel i u och en icke-tom mängd
   exklusiva variabler D. Utgången har därmed formen G(u,H(u,D),Y), där Y
   innehåller övriga variabler. Endast D och u kan upprepas i det utvecklade
   trädet. De måste tillsammans träffa alla mittkanter i punkt 3.

   Vid fixerat u kan tilldelningarna till D därför ge högst två olika
   restfunktioner av Y, en för vartdera värdet på H. Dessutom får D inte
   innehålla en inducerad stig på fyra hörn. Fixera annars u och Y till 0
   och alla andra D-bitar utanför stigen till 0. Utgången blir en
   icke-konstant monoton funktion enbart av H och är alltså H. Denna
   restriktion av H är läs-en-gång, i strid med punkt 3.

Den ändliga kontrollen nedan testar dessa nödvändiga villkor. Ett enskilt
test som överlever villkoren bevisar inget om att en krets finns. När alla
möjligheter har uteslutits ger fallen i punkt 5 och 6 den undre gränsen.

Projektets offentliga uppgift finns i https://data.pequalnp.com/data/desk/gaps.json
och grindmodellen i https://github.com/brilliant-hq/pequalnp-proofs/blob/4b67ba51c4ebd5a11ac116f89149f62d07ccd8fd/lean/PEqualNP/Defs/CircuitLowerBounds.lean
"""

from itertools import combinations


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def subsets(mask):
    part = mask
    while part:
        yield part
        part = (part - 1) & mask
    yield 0


def bitset(vertices):
    return sum(1 << v for v in vertices)


def edge_masks(edges):
    return [bitset(edge) for edge in edges]


def target(assignment, edges):
    return any(assignment & edge == edge for edge in edges)


def extrema(n, edges):
    maximal_zeros = [
        x for x in range(1 << n)
        if not target(x, edges) and all(
            x & (1 << i) or target(x | (1 << i), edges) for i in range(n)
        )
    ]
    return edges + maximal_zeros


def signature_search(n, edges, repetitions):
    # Monotoniciteten ger likhet överallt om de minimala ettorna och maximala
    # nollorna har rätt värde. Varje bit i heltalet står för ett sådant test.
    tests = extrema(n, edges)
    required = (1 << len(edges)) - 1
    variables = [sum(((x >> i) & 1) << k for k, x in enumerate(tests))
                 for i in range(n)]
    positions = variables + [variables[i] for i in repetitions]
    all_positions = (1 << len(positions)) - 1
    possible = [set() for _ in range(all_positions + 1)]
    for i, atom in enumerate(positions):
        possible[1 << i].add(atom)
    for mask in range(1, all_positions + 1):
        if mask.bit_count() == 1:
            continue
        for left in subsets(mask):
            right = mask ^ left
            if not right or not left or left > right:
                continue
            for x in possible[left]:
                for y in possible[right]:
                    possible[mask].update((x & y, x | y))
    # Alla uppdelningar av lövpositioner mellan rotens vänstra och högra
    # underträd har nu provats med både AND och OR.
    return required in possible[all_positions], len(possible[all_positions])


def p4_and_middle_edges(n, edges):
    middle = set()
    induced = []
    for four in combinations(range(n), 4):
        s = bitset(four)
        inside = [e for e in edges if e & s == e]
        degrees = {v: sum(bool(e & (1 << v)) for e in inside) for v in four}
        if sorted(degrees.values()) == [1, 1, 2, 2]:
            induced.append(s)
            middle.add(bitset(v for v in four if degrees[v] == 2))
    return induced, middle


def check_prime_hypotheses(n, edges):
    neighborhoods = []
    for i in range(n):
        row = 0
        for e in edges:
            if e & (1 << i):
                row |= e ^ (1 << i)
        neighborhoods.append(row)
    require(len(set(neighborhoods)) == n, "Lika grannmängder")
    reached = 1
    for _ in range(n):
        for i, row in enumerate(neighborhoods):
            if reached & (1 << i):
                reached |= row
    require(reached == (1 << n) - 1, "Grafen är inte sammanhängande")


def triangle_cuts():
    # Tre ursprungliga linjer 0,1,2, deras tre skärningspunkter 3,4,5
    # och en återstående exklusiv punkt per linje 6,7,8.
    n = 9
    E = edge_masks([(0, 3), (1, 3), (1, 4), (2, 4), (0, 5), (2, 5),
                    (0, 6), (1, 7), (2, 8)])
    check_prime_hypotheses(n, E)
    paths, middle = p4_and_middle_edges(n, E)
    require(len(middle) == 6, "Väntade sex mittkanter")
    mask = (1 << n) - 1
    require(not any(all(s & e for e in middle) for s in subsets(mask) if s.bit_count() <= 2),
            "En vanlig formel med två upprepade bitar har överlevt")
    values = [target(x, E) for x in range(mask + 1)]
    tested = covers = transfers = survivors = 0
    for u in range(n):
        ub = 1 << u
        for D in subsets(mask ^ ub):
            if not D:
                continue
            tested += 1
            if not all((ub | D) & e for e in middle):
                continue
            covers += 1
            Y = mask ^ (ub | D)
            ys = list(subsets(Y))
            good = True
            for value_u in (0, ub):
                distinct = set()
                for d in subsets(D):
                    distinct.add(tuple(values[value_u | d | y] for y in ys))
                    if len(distinct) > 2:
                        good = False
                        break
                if not good:
                    break
            if not good:
                continue
            transfers += 1
            if not any((path & D) == path for path in paths):
                survivors += 1
    require(survivors == 0, "Återstår ett möjligt delningsmönster")
    return tested, covers, transfers, survivors


def verify_star_witness(lines):
    points = sorted(set.union(*lines))
    idx = {p: len(lines) + i for i, p in enumerate(points)}
    n = len(points) + len(lines)
    E = edge_masks([(i, idx[p]) for i, line in enumerate(lines) for p in line])
    gates = []

    def gate(op, left, right):
        number = n + len(gates)
        require(left < number and right < number, "Framåtriktad ledning krävs")
        gates.append((op, left, right))
        return number

    terms = []
    for i, line in enumerate(lines):
        a, b, c, d = [idx[p] for p in sorted(line)]
        point_union = gate("OR", gate("OR", a, b), gate("OR", c, d))
        terms.append(gate("AND", i, point_union))
    output = terms[0]
    for term in terms[1:]:
        output = gate("OR", output, term)
    require(len(gates) == 5 * len(lines) - 1, "Fel grindantal i vittnet")
    for assignment in range(1 << n):
        wires = [(assignment >> i) & 1 for i in range(n)]
        for op, left, right in gates:
            a, b = wires[left], wires[right]
            wires.append(a & b if op == "AND" else a | b)
        require(wires[output] == target(assignment, E), "Avvikelse i grindvittnet")
    return n, len(gates), 1 << n


def main():
    # I L-meta-650 är (p,l) en incidens när p+l mod 13 ligger i D.
    D = {0, 1, 3, 9}
    lines = [{(a - i) % 13 for a in D} for i in range(13)]
    pairs = list(combinations(lines, 2))
    require(all(len(a & b) == 1 for a, b in pairs), "Två linjer ska skära varandra exakt en gång")
    triples = list(combinations(lines, 3))
    concurrent = [t for t in triples if set.intersection(*t)]
    triangles = [t for t in triples if not set.intersection(*t)]
    print(f"Tvålinjersblock {len(pairs)}. Samtidiga tripplar {len(concurrent)}. Övriga tripplar {len(triangles)}.")
    for name, lines_subset in [("två", pairs[0]), ("samtidig trippel", concurrent[0]), ("triangel", triangles[0])]:
        n, gates, assignments = verify_star_witness(lines_subset)
        print(f"Stjärnvittne för {name}: {n} variabler, {gates} grindar, {assignments} tilldelningar verifierade.")

    path = edge_masks([(0, 1), (1, 2), (2, 3), (3, 4)])
    check_prime_hypotheses(5, path)
    hit, count = signature_search(5, path, [])
    require(not hit, "En fyragrindarskrets har överlevt för de två linjerna")
    print(f"Tvålinjersblocket: {count} skilda signaturer med unik lövförekomst, målet saknas.")

    arms = edge_masks([(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (3, 6)])
    check_prime_hypotheses(7, arms)
    results = [signature_search(7, arms, repeat) for repeat in [[]] + [[i] for i in range(7)]]
    require(not any(hit for hit, _ in results), "En sjugrindarskrets har överlevt för den samtidiga trippeln")
    print("Samtidig trippel: skilda signaturer utan extra löv och med ett extra löv på respektive insignal:",
          [count for _, count in results])

    tested, covers, transfers, survivors = triangle_cuts()
    print(f"Triangel: {tested} par (u,D). {covers} täcker mittkanterna. "
          f"{transfers} klarar enbitsöverföring. {survivors} överlever P4-testet.")
    print("Blockens exakta minima är 9, 14 och 14 grindar.")


if __name__ == "__main__":
    main()

