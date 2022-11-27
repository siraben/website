---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

layout: default
---

<!-- display post and dates, and a list of tags for that post -->
{% for post in site.posts %}
  <span style="font-family: monospace;">{{ post.date | date: "%Y-%m-%d" }}</span> [{{ post.title }}]({{ post.url }})
  <!-- put the tags on a new line, each tag should have a little bubble around it -->
    <br>
    <!-- alphabetically sort the tags -->
    {% assign sorted_tags = post.tags | sort %}{% for tag in sorted_tags %}<span style="font-family: monospace; font-size: 0.8em; background-color: #e6e6e6; padding: 0.2em; border-radius: 0.2em;">{{ tag }}</span> {% endfor %}
{% endfor %}