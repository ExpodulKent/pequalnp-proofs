# Tretton punkter, tretton linjer, en lampa
Forskningsanteckning för L-meta-650, 23 november 2026

Börja med fyra knappar. Två knappar betyder ”punkt A” och ”punkt B”. De andra betyder ”linje 1” och ”linje 2”. Anta att A finns på båda linjerna och B bara på linje 2. Vi vill att lampan ska lysa precis när en vald punkt ligger på en vald linje. Trycker du på B och 1 förblir lampan släckt. Trycker du också på A ska den tändas, eftersom A och 1 passar ihop.

Det riktiga pusslet har 13 punktknappar och 13 linjeknappar. Varje punkt ligger på fyra linjer. Det ger 13 × 4 = 52 godkända par. Två olika punkter har exakt en linje gemensamt. Alla 26 knappar får tryckas oberoende av varandra.

## Ett bygge med 64 grindar

För varje punkt samlar vi först dess fyra linjeknappar. Med tre ELLER-grindar kan vi avgöra om minst en av de fyra är intryckt. En OCH-grind kontrollerar sedan om själva punktknappen också är intryckt. Det kostar fyra grindar per punkt, tillsammans 52. Vi har nu tretton delbesked. Att slå ihop dem till ett enda svar kräver tolv ELLER-grindar. Totalt 52 + 12 = 64. Målet i uppgiften är 63 eller färre.

## Varför ett listigt gruppbyte ändå kan gå fel

Tänk dig förslaget ”någon av A och B är vald OCH någon av 1 och 2 är vald”. Gruppen beskriver fyra par på en gång. För att detta ska vara säkert måste alla fyra paren vara godkända. I det lilla exemplet skulle B och 1 tända lampan av misstag. I det riktiga pusslet finns aldrig två olika punkter på två gemensamma linjer. Alltså kan ett sådant säkert gruppbesked samla flera par bara om de har en gemensam punkt eller en gemensam linje. Det ser ut som en stjärna med mitten i den gemensamma knappen.

## Ett bevis för en hel familj av byggen

Anta att bygget består av ELLER-grindar för att samla knappar, följt av ett lager OCH-grindar och till slut ELLER-grindar för att samla gruppbeskeden. Det får finnas delade ledningar och ett par får täckas flera gånger. Vi räknar användbara gruppbesked. Ett som aldrig kan bidra får strykas. Ett OCH som får en konstant etta kan förenklas. Ett kvarvarande besked är ”någon ur lista A OCH någon ur lista B”. En knapp kan inte finnas på båda listorna, eftersom en ensam knapp då tänder lampan. Alla par över listorna måste vara kanter. Därför är varje gruppbesked en stjärna, också när grupperna valts från båda sidor. Om ett besked gäller bara ett par får vilken som helst av dess två knappar vara dess mitt.

Skriv t för antalet sådana OCH-grindar. Det finns tretton godkända par som inte delar en enda knapp, till exempel punkt 0 med linje 0, punkt 1 med linje 12, punkt 2 med linje 11 och så vidare. En stjärna kan bara täcka ett av dessa par. Därför är t minst 13.

För varje stjärnmitt räknar vi hur många olika grannar som förekommer i dess besked. Kalla detta antal d och antalet besked från samma mitt b. För att samla d olika knappar i b utgående listor behövs minst d − b ELLER-grindar. Man kan tänka på d lösa trådar. En grind som förenar två grupper kan minska antalet åtskilda grupper med högst ett. Även med delade resultat behöver varje ingång kunna nå en av de b utgångarna. Det ger samma räkning. En grind som redan samlat två olika grannar kan inte hjälpa en annan stjärnmitt, eftersom två mittknappar har högst en gemensam granne. En onödig ELLER som representerar en ensam knapp kan förenklas till en tråd.

När vi summerar över alla mittknappar blir summan av d minst 52, eftersom varje kant måste täckas. Summan av b är t. I början behövs därför minst 52 − t grindar. Mitten har t OCH-grindar. På slutet behövs minst t − 1 ELLER-grindar för att de t beskeden ska kunna nå utgången. Summan är minst 52 + t − 1, alltså minst 64.

## Var tog det stopp?

I en allmän krets får ett OCH-besked skickas in i fler OCH- och ELLER-grindar i flera omgångar. Då kan den första mellanberäkningen lysa för ett felaktigt par som en senare grind stoppar. Vårt räknebevis använde att varje stjärnas besked direkt får tända slutlampan. Det antagandet gäller inte längre. Ett motexempel med 63 grindar måste därför använda en metod som går utanför formen ovan. Om det går står öppet i vårt arbete.

## Vad datorn har kontrollerat

Kör ”node Kontrollera-64.cjs”. Programmet läser uppgiftens 52 par, kontrollerar de tretton disjunkta paren och att två punkter alltid har exakt en gemensam linje. Det bygger de 64 grindarna och räknar fram precis vilka minsta knappkombinationer som kan tända utgången. Det blev exakt de 52 par vi vill ha. Eftersom kretsen bara har OCH och ELLER förblir lampan tänd om fler knappar trycks. Kontrollen gäller därför alla knappkombinationer.

Programmet går även igenom alla 8 192 val av punktknappar som stjärncentra. För varje val räknar det vilka linjeknappar som då måste vara centra för att täcka resten. Exakt två täckningar använder bara tretton centra, antingen alla punkter eller alla linjer. Programmet kontrollerar det uttryckliga bygget och de ändliga räkningarna. Argumentet om alla byggen med ett OCH-lager ovan är ett handbevis.

## Projektets uppgift

https://pequalnp.com/lemma#L-meta-650

## Kan man spara en grind genom att bygga om några linjer?

Vi undersökte också två eller tre linjer i taget. Här får man blanda OCH och ELLER fritt och återanvända en tidigare grind flera gånger inom blocket. Ett fristående block får bara sina egna knappar som ingångar.

Det finns 78 par av linjer. Två linjer möts alltid i en punkt, och ett sådant block behöver exakt 9 grindar. Tre linjer kan antingen mötas i en och samma punkt eller bilda tre olika skärningspunkter. Det finns 52 respektive 234 sådana val. I båda fallen behövs exakt 14 grindar. I programfilen finns handargumentet som begränsar vilka kopplingar som måste prövas och den ändliga uppräkningen som kontrollerar fallen. Ett block som får använda en färdig signal från andra delar av kretsen faller utanför resultatet. Hela frågan om 63 grindar är fortfarande öppen i vårt arbete.

[Kontrollera 64-grindskretsen med Node.js](Kontrollera-64.cjs) · [Läs handbeviset och kör blockkontrollen med Python](650-lokalsyntes.py)
