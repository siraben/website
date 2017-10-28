---
layout: post
title:  "Hello, world!"
date:   2017-10-28 21:36:29 +0900
categories: update
---
# Header 1
## Header 2

### Header 3
#### Header 4
##### Header 5
###### Header 6

[My favorite search engine.](https://ddg.gg)

Since it's Markdown, it's possible to have text **bold**, _italicized_ __*or even both!*__


|   This   |    is     |   a   |
| :------: | :-------: | :---: |
|   test   |    of     |  the  |
|  table   | rendering |  in   |
| Jehykll. |   Very    | nice! |


### C Code Syntax Highlighting
```c
int main(void)
{
    printf("hello, world!\n");
    return 0;
}
```

### Javascript Bookmarklet that calculates GPA
```javascript
javascript:(function(){var d=function(){var a=Array.prototype.map.call(document.getElementsByClassName("linkDescList grid"),function(a){return Array.prototype.map.call(a.querySelectorAll("td"),function(a){return a.innerHTML})});a=function(a,b){for(var c=[],e=0,f=a.length;e<f;)c.push(a.slice(e,e+=b));return c}(a[0],16);for(var e=0,f=0,k={7:4.3,6:4,5:3.3,4:2.3,3:1.3,2:0,1:0},h=0,b=0;b<a.length;b++){var c=a[b][12].match(/<a\s+href="[\S\s]*?">[\S\s]*?<\/a>/gi);if(null==c)break;c=parseInt(c[0].replace(/(<\/?[^>]+>)/gi,""));
e++;f+=k[c];"IB"!=a[b][11].substring(0,2)&&"AP"!=a[b][11].substring(0,2)||"IB Math Studies"==a[b][11].substring(0,15)||(f+=.5);h+=c}return[h/e,f/e]}(),g="(S1) GPA: "+d[0].toFixed(3);d="Traditional GPA: "+d[1].toFixed(3);var l=document.createElement("p");l.style.fontSize="20px";l.style.fontFamily="Helvetica";l.style.textAlign="center";l.style.marginBottom="-5px";l.appendChild(document.createTextNode(g));l.appendChild(document.createElement("br"));l.appendChild(document.createTextNode(d));document.getElementsByTagName("tbody")[2].appendChild(l);})();
```

