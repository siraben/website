---
layout: post
title: Market making in Minecraft
subtitle: How I arbitraged lots of virtual money, and how you can, too!
tags:
- minecraft
- economics
date: 2022-11-08 14:24 -0600
---
Admist all this talk of market making and economics, one idle evening
during the summer of 2022 I wondered, "could I do arbitrage on a
Minecraft server?"  The answer was not only yes, but it was incredible
to witness the extent to which by doing essentially nothing but trades
I was able to accumulate tens of thousands in virtual currency.  I'm
not going to say which server this was performed on, but it should be
straightforward to do the same in other economy-based servers.

**Note: after essentially exercising all the arbitrage that
was possible, a week later prices converged and it was much harder to
do.**

## All's fair in love and markets

What's the price of a block of cobblestone?  What about the price of
gold?  There are some heuristics that can help determine pricing, for
instance iron blocks consist of 9 iron bars, so any price discrepancy
would quickly be ironed out by arbitrage.  Diamonds feel like they
should be pricey, but maybe it's unclear what would consistute a
"fair" price.  Fortunately, economics has the answer to this: let the
market decide!

Several Minecraft servers have a buy/sell plugin in which a shopkeeper
can stock up a chest with a desired item and set it to buy or sell the
item.  Some shops even have buy and sell chests for the same item.  Of
course, no one would be naïve enough to allow arbitrage to be
exercised against themselves, so the spreads I observed were always
ridiculous, and rightly so.  If I don't really need much of an item,
why would be buying it at a high price from people and risk
bankruptcy?

But there is no limit to how many stores can be opened and how things
are priced.  This is where arbitrage comes in.  To make matters
easier, there are no transaction fees, and the transactions happen
instantly.  There was also a warp system that conveniently allowed me
to teleport to any market that people advertised on a list.

## Let's trade
The game, then, was straightforward.  Go around collecting buy/sell
information from various shops, just as in real markets, observe where
a buy price is higher than a sell price, then do the trade.

Here's a graph showing the net profits after 117 trades.

![Graph showing the net profit and trades over
time](/assets/trades.png)

For completeness, this is how the transactions looked when I recorded
them.  The only unfortunate thing is that from time to time I
bankrupted some users (RIP iced logs).


| item          | shop                   | quantity | price |   amt | net profit |
|---------------|------------------------|---------:|------:|------:|-----------:|
| gunpowder     | spawners and more      |       15 |   -10 |  -150 |    12551.2 |
| gunpowder     | killashop              |       15 |    15 |   225 |    12776.2 |
| oak log       | stellvia               |      114 |    -4 |  -456 |    12320.2 |
| oak planks    | iced logs              |      456 |     2 |   912 |    13232.2 |
| birch log     | stellvia               |      432 |    -4 | -1728 |    11504.2 |
| birch planks  | iced logs              |     1728 |     2 |  3456 |    14960.2 |
| spruce planks | celt                   |     1472 |    -1 | -1472 |    13488.2 |
| spruce planks | iced logs (bankrupted) |      162 |     2 |   324 |    13812.2 |

It was also interesting to observe market changes in real time.  In
one particular instance, gunpowder was being sold by the hundreds from
a shop pricing them at $5 each, which was clearly a steal given that
another shop is happily buying them at $15.  After messaging the
shopkeeper several times as I kept buying them out of gunpowder, I
watched as the price rose to $7.5 then $10.  That's price convergence
right there.

## Future directions
Some thought experiments that I did not implement but might serve as
suggestions for the interested reader:

- Write a bot to automatically warp to every shop and scrape the sign
  data
- Write a bot that exercises the arbitrage automatically (recommended:
  use state-of-the-art pathfinding bots such as baritone)
