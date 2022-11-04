---
layout: post
title: SekaiCTF 2022 Writeup - Matryoshka
tags:
- ctf
date: 2022-10-02 08:43 -0500
---

ANSI escape codes.  Race conditions in PNG parsing.  Digital COVID-19
vaccination records.  De-noising audio files and the NATO phonetic
alphabet.  The only thing linking all of them?  A race to solve a CTF
challenge and get the flag.

This past weekend I had a lot of fun participating in [SekaiCTF
2022](https://ctf.sekai.team/).  This post will dive into a particular
problem our team found interesting and were quick to solve (we were
the 5th solve out of 800+ teams that participated and 12 eventual
solves for this question).

As the name implies, Matryoshka (матрёшка) refers to Russian nesting
dolls.  In the context of CTFs, this probably was hinting at the
multi-layered nature of the problem, an appreciated nudge since we are
pressed for time during competitions.

## Setup

We were given two PNG files and the following bullet points.

`Matryoshka.png`             |  `Matryoshka-Lite.png`
:-------------------------:|:-------------------------:
![Matryoshka](/assets/Matryoshka.png)  |  ![Matryoshka-Lite](/assets/Matryoshka-Lite.png)


- [x] One extra bit will double the 8 colors you already have, but
  ain't these new colors too similar to the old ones?
- [x] "Never reinvent your own wheel", people say. But Apple insisted
  on thinking differently when parsing PNGs.
- [ ] ?
- [ ] ?

This proved intriguing, since the screenshots appeared to show all
that was necessary---the code, example run and what potentially could
be the flag or next step.  We see what appears to be VS Code windows
with a dark, high-contrast theme on, Python code and colored text in a
terminal, presumably generated from the same code.

The first bullet point refers to the fact that adding another bit to a
string doubles the number of possible messages that could be conveyed.
In this case, there are 8 color and 16 possibilities for terminal
colors that would use 3 and 4 bits respectively.

The second bullet point I recognized as a possible reference to a
phenomenon I [saw on Hacker
News](https://news.ycombinator.com/item?id=29573792) 9 months ago,
where the way that Apple software implemented PNG parsing had a race
condition that could be exploited to cause PNG images to render
differently than they would on other platforms.  Though, no signs of
that quite yet.

## A very ANSI adventure
[This
resource](https://gist.github.com/fnky/458719343aabd01cfb17a3a4f7296797)
was very helpful while brushing up on the ever-so-niche ANSI escape
codes that have cryptic syntax.

### Messages through ANSI color codes
Of course, I immediately transcribed the code, changed VS Code's color
settings and replicated the output.  I chose to stick with the
`Matryoshka-Lite` image because no foreground was being set and so I
would only have to sample one color, and changed the smiley face to a
dot.

```python
import sys
stdin = sys.stdin.buffer.read()
d = "".join(bin(i)[2:].zfill(8) for i in stdin)
p = ""
for i in range(0, len(d), 8):
    l = d[i:i+4]
    h = d[i+4:i+8]
    he = 40 if h[0] == "0" else 100
    he += int(h[1:], 2)
    le = 40 if l[0] == "0" else 100
    le += int(l[1:], 2)
    p += f"\033[{he}m●\033[0m"
    p += f"\033[{le}m●\033[0m"
print(p)
```

The Japanese sentence あなたと私でランデブー？[(You and me,
rendezvous?)](https://www.youtube.com/watch?v=HOz-9FzIDf0) also
provided a sanity check that the code was executing correctly.  Being
somewhat of a hobby linguist, I noticed immediately that the character
`？` was the [FULLWIDTH QUESTION MARK
character](https://en.wikipedia.org/wiki/Question_mark#Fullwidth_question_mark_in_East_Asian_languages)
which is used in East Asian languages.  This was important in making
sure that the outputs matched exactly.

![My replication of the screenshot](/assets/matryoshka-replicate.png)

### Decrypting the block cipher
Cryptography wise, this was a relief.  It's immediately evident that
this is a mere block cipher.  To walk through an example,
consider what happens when we start with the string `fl`.  First we
convert the [scalar
values](https://unicode.org/glossary/#unicode_scalar_value) (not
bytes!)  into binary numbers and leftpad them with zeroes.


```python
>>> [bin(i)[2:].zfill(8) for i in "fl".encode()]
['01100110', '01101100']
```

Next we join the strings then take blocks `l` and `h` of size 4 each
time.  We check if the first digit is a 0 or 1 and adjust the value
accordingly and add the remaining bits to either 40 or 100.  Observe
that since the maximum value of the remaining bits is 7, we can easily
reverse the process to go back to the original block.  Adjacent blocks
are also transposed as we go along which was a bit unusual but did not
affect the reversing process.  This is the algorithm I wrote:

```python
# inverse of encode
def decode(d):
    # reconstruct the first bit
    if d >= 100:
        d -= 100
        b = "1"
    else:
        d -= 40
        b = "0"
    # reconstruct the last 3 bits then concat
    return b + bin(d)[2:].zfill(3)
```

### From color to data
Now that I had the algorithm to decrypt the cipher, I looked at the
image and had to decide how to go from the colors shown into the array
of numbers to decode.  Since CTFs are time-sensitive, I literally just
used macOS's Color Picker utility and keyboard shortcuts to go through
the colored rectangles one by one and paste them into Emacs.  It would
be disastrous to miss or repeat a color, so I found some [Emacs Lisp
code](https://www.emacswiki.org/emacs/HexColour) that would highlight
the hex colors in `text-mode` buffers for ease of viewing.

![Customizing Emacs to view hex
colors](/assets/emacs-font-lock-hex.png)

So now we have a list of hex colors.  Then, a bit of Emacs-fu and
visual cross-checks allowed me to obtain the list of numbers.

```python
enc = []
with open("data.txt") as f:
    for line in f:
        enc += [int(line)]
w = []
for i in range(0, len(enc), 2):
    w += [chr(int(decode(enc[i+1]) + decode(enc[i]),2))]
print("".join(w))
```

Decoding becomes a piece of cake.  We obtain the URL
`https://matryoshka.sekai.team/-qLf-Aoaur8ZVqK4aFngYg.png`, which is
the following image:

![Matroyshka stage 2](/assets/matryoshka-stage2.png)

## Think Different(ly about PNG parsing)
I encourage you to scan the QR code.  Things were looking a bit duller
at this point.  What's with the noisy lines across the image?  We
spent a few minutes trying to collect the lines together and discern
patterns in it, but no dice.

Then I remembered the clue from earlier.  Unfortunately (or
fortunately), my macOS version is far too new to have the bug, and
several teammates were using Windows laptops.  However,
[Nisala](https://github.com/nkalupahana) hadn't updated his Mac in a
while, and we were pleasantly surprised when we saw Safari correctly
incorrectly rendering the PNG:

![Matroyshka stage 3](/assets/matryoshka-stage3.png)

Bingo.  Now when we scan the QR code, instead of a funny YouTube video
we have this string:

```
shc:/56762959532654603460292540772804336028702865676754222809286237253760287028647167452228092863457452621103402467043423376555407105412745693904292640625506400459645404280536627540536459624025250555056338566029120106413333400028742635076939734552056936583171064558751131556353203754372575033328200705643838552934743139500009536061356931346955643709527105115665600005602172234467374542085807222475347132034424395261373056004444002400085237353061222027453167672627082630290769235375711135114127401104212540537525556303742533507136503255653563264154433970205436100050743522116306752331635775741156433654585503107626684254686208403754634470273768056171327607656125712725523234611005361121030308333867583166536725643767425270646323270003005623700860226659203405252357762043663326362209257233442225631073757558424358121058221221247175065067275426364058293454221133236771205077255211441131752363046604226175031256730654443172527522070726232026532434301128375372255668000400627667676055323160225036622041105858255222692922334259596624276377446745261173582545412027102861666538363053246255715622773453607507284404720407630733005623703641432800427011066429357722525365740010257264576557765569557135536228273331723728623059574332602964335058526177070375095735563159552930336664240727603959105433044575393334503567543958542929065332126645230910313334672722391208422438276434441236775655650958267743437110394352455760210354655321596331533463522358444058636442336866670845305568693721662269635473434227715411302507646165766341072469394221072671236868392755064436586159754123754210552170093809524555337700313654703040673106437576344009087611676326535274567421423023706811744311775220407005454032310440346554616620552130066153666738533667226435276755422240350073103639763904405705005555244371301010730641435756764057646755286006396271642377067569577743576669054164110561644535096843257762673432272976686542737404354077010832356003656226634535455971326660756506220359605868077353056052347436404527397258656831553804624139525240420467593362371139026720436433630272626572681040385977300452644174
```

## Fully vaccinated
Scanning it with my iPhone I saw that it was a COVID-19 vaccination
record, but nothing really seemed out of the ordinary.  Then
[Akash](https://github.com/Ace314159) found a [Smart Health Card
parser](https://bramp.github.io/smart-health-card-scanner/) where we
pasted in the raw contents.

We spotted an unusual entry in the contact information for the
patient---a base64 encoded string.

```js
...
contact: [
   {
      name: {
         text: "flag"
      },
      telecom: [
         {
            system: "url",
            value: "data:text/html;base64,PGF1ZGlvIHNyYz0iaHR0cHM6Ly9tYXRyeW9zaGthLnNla2FpLnRlYW0vOGQ3ODk0MTRhN2M1OGI1ZjU4N2Y4YTA1MGI4ZDc4OGUud2F2IiBjb250cm9scz4="
         }
      ]
   }
]
...
```

Onto the next stage!

## All about that base
Let's decode the base64.
```
$ echo 'PGF1ZGlvIHNyYz0iaHR0cHM6Ly9tYXRyeW9zaGthLnNla2FpLnRlYW0vOGQ3ODk0MTRhN2M1OGI1ZjU4N2Y4YTA1MGI4ZDc4OGUud2F2IiBjb250cm9scz4=' | base64 -d
<audio src="https://matryoshka.sekai.team/8d789414a7c58b5f587f8a050b8d788e.wav" controls>
```

Hm, an [audio
file](https://matryoshka.sekai.team/8d789414a7c58b5f587f8a050b8d788e.wav)
(**warning: loud noise**).  This was the most experimental of all the
stages.  At first it seemed like just noise but on closer listening we
could faintly hear a human voice speak in regular intervals.  It
doesn't show up on a spectrogram however:

![Spectrogram of the WAV file](/assets/matryoshka-audacity.png)

### Finding the signal in the noise
By now half of our team was listening to parts of the audio file and
messing around with various audio settings such as equalization and
noise reduction.  To be clear, none of us are audio engineers by
training so this was a do-what-feels-right kind of deal.  Eventually,
we found a website that did noise reduction and put the audio file
through it *5* times, then, to our continual surprise (which was
routine at this point), this is what we saw and heard:

![Five times cleaned audio file](/assets/matryoshka-cleaned.png)

Now the words were very clear.  The words corresponded to the [NATO
phonetic
alphabet](https://en.wikipedia.org/wiki/NATO_phonetic_alphabet) and it
was far easier to now transcribe the message, which was the flag,
`SEKAI{KandoRyoko5Five2Two4Four}`.

## Conclusions and feedback
The question was really well-designed, and was a refreshing format to
see in a CTF competition which is often dominated by more traditional
reverse engineering.  I do want to highlight some things I thought
were great to see:

- Relying on colors can be a risky design choice, but the uniformity
  of VS Code and using a default theme was helpful
- The hints about Apple-specific PNG rendering were good but
  potentially hard to overcome if the team did not have access to
  Apple hardware that was unpatched

I hope you enjoyed reading this post as I much as I enjoyed the
process of working with my teammates and finding the flag!
