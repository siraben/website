---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

layout: base
---

{% for post in site.posts %}
  <span class="post-date">{{ post.date | date: "%Y-%m-%d" }}</span> [{{ post.title }}]({{ post.url }})
    <br>
    {% assign sorted_tags = post.tags | sort %}{% for tag in sorted_tags %}<span class="post-tag">{{ tag }}</span> {% endfor %}
{% endfor %}